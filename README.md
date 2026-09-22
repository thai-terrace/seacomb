# seacomb

Formally verified, `libseccomp`-compatible Rust library for enforcing seccomp policies.

Supported architectures: x86, x86_64, ARM, and AArch64.

```
cargo verus verify/build
```

# Testing

Install dependencies: Lima, QEMU, `cargo-zigbuild`, and Zig.
```sh
# For macOS
brew install lima qemu
python3 -m venv target/cross-tools
target/cross-tools/bin/pip install cargo-zigbuild==0.23.4 ziglang==0.16.0
```

To run all tests on one or all supported architectures:
```sh
python3 tests/run.py
python3 tests/run.py aarch64
```
