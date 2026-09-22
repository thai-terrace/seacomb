# seacomb

A *formally verified* Rust library for compiling and enforcing seccomp policies,
with a similar interface to `libseccomp`.

Supported architectures: x86, x86_64, ARM, and AArch64.

To verify all proofs and build:
```
cargo verus build
```

# Testing

First install QEMU (e.g., `brew install qemu`).

To run all tests on all or one specific supported architectures:
```sh
python3 tests/run.py
python3 tests/run.py aarch64
```
