# seacomb

`seacomb` is a Rust library for compiling and enforcing
[seccomp](https://man7.org/linux/man-pages/man2/seccomp.2.html) policies
(i.e., for filtering/intercepting Linux syscalls and sandboxing).

By declaring rules in a similar style to [libseccomp](https://github.com/seccomp/libseccomp),
`seacomb` compiles and registers these rules using a *formally verified* compiler to cBPF.

```rust,no_run
use seacomb::*;

// Set default action to killing the process.
let mut filter = Filter::new_native(Action::KillProcess).unwrap();

filter.add_rule(Action::Allow, Syscall::Read, vec![]).unwrap();
filter.add_rule(Action::Allow, Syscall::ExitGroup, vec![]).unwrap();

// Allow write(2) to stdout (fd 1) only.
filter.add_rule(Action::Allow, Syscall::Write, vec![ArgCmp::eq(0, 1)]).unwrap();

// Make openat(2) fail with EACCES.
filter.add_rule(Action::Errno(13), Syscall::Openat, vec![]).unwrap();

#[cfg(target_os = "linux")]
filter.install().unwrap();
```

## What has been formally verified

`seacomb` is developed using [Verus](https://github.com/verus-lang/verus),
an automated program verifier for Rust.

Formally verified properties:
- **Compiler correctness:** `seacomb`'s policy compiler always produces cBPF filters equivalent to the source policy, relative to the formal semantics of policies and cBPF in `src/spec`.
  This rules out miscompilations like these in libseccomp:
  - [CVE-2019-9893](https://github.com/seccomp/libseccomp/issues/139):
    64-bit `<`, `<=`, `>`, `>=` argument comparisons were generated incorrectly,
    so filters could be bypassed.
  - [#148](https://github.com/seccomp/libseccomp/issues/148):
    the optimizer merged code blocks that were not actually duplicates,
    which broke Tor's sandbox.
  - [GHSA-4q85-33p6-j5g6](https://github.com/seccomp/libseccomp/security/advisories/GHSA-4q85-33p6-j5g6):
    merging overlapping 64-bit comparison rules let denied syscalls through.
- **Determinism:** A policy picks exactly one action for each syscall.
- **Chaining:** Installing multiple policies is equivalent to evaluating them
  in order, verified against the kernel's precedence and tie-breaking rules.

To verify the proofs, [install Verus](https://github.com/verus-lang/verus/blob/main/INSTALL.md),
and run:
```sh
cargo verus verify
```
Without verification, this crate is also completely compatible with `cargo`.

## Testing

QEMU is a prerequisite for testing (install with, e.g., `brew install qemu`).

To run all tests on all supported architectures, or on one:
```sh
python3 tests/run.py
python3 tests/run.py aarch64
```
