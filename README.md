# seacomb

Formally verified, `libseccomp`-compatible Rust library for enforcing seccomp policies.

```
cargo verus verify/build
```

# Testing

Dependencies: `qemu` and `lima-additional-guestagents`.

```
ARCH=x86_64
TARGET=x86_64-unknown-linux-gnu

limactl start --tty=false --name=seacomb-$ARCH lima/$ARCH.yaml
limactl shell seacomb-$ARCH cargo test --target $TARGET

# Optional clean up
limactl delete -f seacomb-$ARCH
```

Supported architectures:
| `ARCH`    | `TARGET`                        |
| --------- | ------------------------------- |
| `x86_64`  | `x86_64-unknown-linux-gnu`      |
| `x86_64`  | `i686-unknown-linux-gnu`        |
| `x32`     | `x86_64-unknown-linux-gnux32`   |
| `aarch64` | `aarch64-unknown-linux-gnu`     |
| `armv7l`  | `armv7-unknown-linux-gnueabihf` |

NOTE: `x32` takes one restart before the first test run, for the guest to come up on
the kernel command line that turns the ABI on:
```
limactl stop seacomb-x32 && limactl start --tty=false seacomb-x32
```
