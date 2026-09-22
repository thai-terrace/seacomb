#!/usr/bin/env python3
import argparse
import fcntl
import json
import os
import platform
import subprocess
import sys
import time
from pathlib import Path

TESTS = Path(__file__).resolve().parent
ROOT = TESTS.parent
# musl targets link statically with the toolchain's rust-lld, so no cross linker is needed.
TARGETS = {
    "x86_64": ("x86_64", "x86_64-unknown-linux-musl"),
    "i686": ("x86_64", "i686-unknown-linux-musl"),
    "aarch64": ("aarch64", "aarch64-unknown-linux-musl"),
    "armv7l": ("armv7l", "armv7-unknown-linux-musleabihf"),
}


def run(*args, capture=False, timeout=None, ok=(0,)):
    result = subprocess.run(args, text=True, cwd=ROOT, timeout=timeout,
                            stdout=subprocess.PIPE if capture else None)
    if result.returncode not in ok:
        result.check_returncode()
    return result.stdout


def lima(*args, **kwargs):
    return run("limactl", *args, **kwargs)


def build(target):
    output = run("cargo", "test", "--no-run", "--locked", "--target", target,
                 "--config", f'target.{target}.linker="rust-lld"',
                 "--target-dir", str(ROOT / "target/cross-tests"),
                 "--message-format=json-render-diagnostics", capture=True)
    artifacts = [json.loads(line) for line in output.splitlines() if line.startswith("{")]
    binaries = [a["executable"] for a in artifacts if a.get("reason") == "compiler-artifact"
                and a["profile"]["test"] and a.get("executable")]
    if not binaries:
        sys.exit(f"No test executables built for {target}.")
    return binaries


parser = argparse.ArgumentParser(description="Build tests on the host and run them in Lima.")
parser.add_argument("arch", nargs="?", default="all", choices=["all", *TARGETS])
args = parser.parse_args()
host = {"arm64": "aarch64", "AMD64": "x86_64"}.get(platform.machine(), platform.machine())
groups = {}
for arch in TARGETS if args.arch == "all" else [args.arch]:
    template, target = TARGETS[arch]
    groups.setdefault(template, []).append((arch, target))

try:
    lima_home = Path(os.environ.get("LIMA_HOME", Path.home() / ".lima"))
    lima_home.mkdir(parents=True, exist_ok=True)
    # Keep the lock file; the OS releases the lock even if the runner is killed.
    with (lima_home / ".seacomb-tests.lock").open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print("Waiting for another seacomb test run...", flush=True)
            fcntl.flock(lock, fcntl.LOCK_EX)
        started = time.monotonic()
        existing = set(lima("list", "--quiet", capture=True).splitlines())
        for template, targets in groups.items():
            binaries = [(arch, binary) for arch, target in targets for binary in build(target)]
            vm = f"seacomb-{template}"
            if vm in existing:
                lima("start", "--tty=false", vm)
            else:
                driver = ["--vm-type=qemu"] if template != host else []
                lima("start", "--tty=false", f"--name={vm}", *driver, str(TESTS / f"{template}.yaml"))
                existing.add(vm)
            try:
                # Exit 2 means cloud-init finished with recoverable warnings.
                lima("shell", "--workdir=/", vm, "cloud-init", "status", "--wait", timeout=600, ok=(0, 2))
                guest_dir = lima("shell", "--workdir=/", vm, "mktemp", "-d", capture=True).strip()
                for arch, binary in binaries:
                    print(f"\n==> Testing {arch} ({vm})", flush=True)
                    lima("copy", "--backend=scp", binary, f"{vm}:{guest_dir}/tests")
                    lima("shell", f"--workdir={guest_dir}", vm, f"{guest_dir}/tests")
            finally:
                lima("stop", "--tty=false", vm)
        print(f"\nAll selected tests passed in {time.monotonic() - started:.1f}s (including provisioning and shutdown).")
except subprocess.CalledProcessError as error:
    sys.exit(error.returncode)
except subprocess.TimeoutExpired:
    sys.exit("Timed out waiting for VM provisioning.")
except OSError as error:
    sys.exit(str(error))
except KeyboardInterrupt:
    sys.exit(130)
