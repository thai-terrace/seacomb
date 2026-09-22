# seacomb

A *formally verified* Rust library for compiling and enforcing seccomp policies,
with a similar interface to `libseccomp`.

Supported architectures: x86, x86_64, ARM, and AArch64.

```
# Verify proofs and build
cargo verus build
```

# Testing

Install dependencies: Lima and QEMU.
```sh
# For macOS
brew install lima qemu
```

To run all tests on one or all supported architectures:
```sh
python3 tests/run.py
python3 tests/run.py aarch64
```
