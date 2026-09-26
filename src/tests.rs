//! Tests of filter construction and native seccomp enforcement.

use crate::{CheckError, Error, Filter};
use crate::spec::cbpf::{AluOp, Instr, Src};
use crate::spec::policy::{Action, Arch, ArgCmp, Rule};
use crate::spec::syscall::Syscall;

impl Syscall {
    /// Returns the native six-argument mmap entry point.
    fn native_mmap() -> Self {
        if cfg!(target_pointer_width = "64") { Self::Mmap } else { Self::Mmap2 }
    }
}

#[test]
fn native_constructor_adds_only_native() {
    let mut filter = Filter::new_native(Action::Errno(7)).unwrap();
    let native = Arch::native().unwrap();
    assert!(matches!(filter.add_arch(native), Err(Error::Check(CheckError::DuplicateArch))));
    for arch in [Arch::X86, Arch::X86_64, Arch::Arm, Arch::Aarch64] {
        if arch != native {
            filter.add_arch(arch).unwrap();
        }
    }
    assert!(matches!(
        Filter::new_native(Action::Errno(4096)),
        Err(Error::Check(CheckError::InvalidErrno(_)))
    ));
}

#[test]
fn cloned_filters_can_be_customized_independently() {
    let syscall = Syscall::native_mmap();
    let action = Action::Errno(13);
    let mut condition = ArgCmp::eq(0, 1);
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter.add_rule(action, syscall, vec![condition]).unwrap();
    let original_program = filter.policy.to_cbpf().unwrap();

    let mut cloned = filter.clone();
    assert_eq!(cloned, filter);
    assert_eq!(cloned.policy.to_cbpf().unwrap(), original_program);

    condition.a = 2;
    cloned.add_rule(action, syscall, vec![condition]).unwrap();
    cloned.enable_thread_sync();

    assert_ne!(cloned, filter);
    assert_eq!(filter.policy.to_cbpf().unwrap(), original_program);
    assert_ne!(cloned.policy.to_cbpf().unwrap(), original_program);
}

#[test]
fn seven_conditions_compile() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    let conds = (0..7).map(|arg| ArgCmp::eq(arg % 6, 0)).collect();
    filter.add_rule(Action::Errno(1), Syscall::native_mmap(), conds).unwrap();
    assert!(filter.policy.to_cbpf().is_ok());
}

#[test]
fn rules_allow_matching_and_different_default_payloads() {
    for (default, same, different) in [
        (Action::Errno(1), Action::Errno(1), Action::Errno(2)),
        (Action::Trace(0), Action::Trace(0), Action::Trace(u16::MAX)),
        (Action::Trap(0), Action::Trap(0), Action::Trap(u16::MAX)),
    ] {
        let mut filter = Filter::new_native(default).unwrap();
        filter.add_rule(same, Syscall::Getpid, vec![]).unwrap();
        filter.add_rule(different, Syscall::Getpid, vec![]).unwrap();
    }
}

#[test]
fn action_payload_boundaries() {
    for action in [
        Action::Errno(0),
        Action::Errno(4094),
        Action::Errno(4095),
        Action::Trace(u16::MAX),
        Action::Trap(u16::MAX),
    ] {
        let mut filter = Filter::new_native(Action::Allow).unwrap();
        filter.add_rule(action, Syscall::Getpid, vec![]).unwrap();
    }
    for errno in [4096, u16::MAX] {
        assert!(matches!(
            Filter::new(Action::Errno(errno)),
            Err(Error::Check(CheckError::InvalidErrno(_)))
        ));
    }
}

#[test]
fn oversized_program_compiles() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    for val in 0..1000 {
        filter
            .add_rule(Action::Errno(13), Syscall::native_mmap(), vec![ArgCmp::eq(0, val)])
            .unwrap();
    }
    let program = filter.policy.to_cbpf().unwrap();
    assert!(program.instrs.len() > 4096);
    #[cfg(target_os = "linux")]
    assert_eq!(Child::run_unfiltered(|| {
        if !matches!(filter.install(), Err(Error::FilterTooLarge)) {
            return 1;
        }
        0
    }), Child::Exited(0));
}

#[cfg(target_os = "linux")]
#[test]
fn installation_checks_instruction_limit_before_side_effects() {
    // Use a fixed architecture so the emitted lengths are host-independent.
    // The final case would wrap to 1 when cast to sock_fprog.len.
    for (len, rule_count, condition_count) in [(4096, 1362, 1), (4097, 1361, 2), (65537, 21841, 2)] {
        let mut filter = Filter::new(Action::Allow).unwrap();
        filter.add_arch(Arch::Aarch64).unwrap();
        filter.on_bad_arch(Action::Allow).unwrap();
        for i in 0..rule_count {
            let conds = if i == 0 {
                (0..condition_count).map(|_| ArgCmp::eq(0, 0)).collect()
            } else {
                vec![]
            };
            filter.add_rule(Action::Allow, Syscall::Mmap, conds).unwrap();
        }
        assert_eq!(filter.policy.to_cbpf().unwrap().instrs.len(), len);
        let child = Child::run_unfiltered(|| {
            // SAFETY: PR_GET_NO_NEW_PRIVS takes scalar arguments and returns the flag directly.
            let before = unsafe { libc::prctl(libc::PR_GET_NO_NEW_PRIVS, 0, 0, 0, 0) };
            if before < 0 {
                return 1;
            }
            let result = filter.install();
            if len == 4096 {
                return if result.is_ok() { 0 } else { 2 };
            }
            if !matches!(result, Err(Error::FilterTooLarge)) {
                return 3;
            }
            // SAFETY: PR_GET_NO_NEW_PRIVS takes scalar arguments and returns the flag directly.
            let after = unsafe { libc::prctl(libc::PR_GET_NO_NEW_PRIVS, 0, 0, 0, 0) };
            if after != before {
                return 4;
            }
            0
        });
        assert_eq!(child, Child::Exited(0), "instruction count: {len}");
    }
}

/// How a child process that ran under a filter ended.
#[cfg(target_os = "linux")]
#[derive(Debug, PartialEq, Eq)]
enum Child {
    /// Left through `_exit` with this status.
    Exited(i32),
    /// Killed by this signal.
    Killed(i32),
}

#[cfg(target_os = "linux")]
impl Child {
    /// The status the child leaves with when the filter never reaches the kernel.
    const INSTALL_FAILED: i32 = 70;

    /// The errno the last failing libc call left behind.
    fn errno() -> i32 {
        std::io::Error::last_os_error().raw_os_error().unwrap_or(0)
    }

    /// Runs `body` in a child process that has `filter` installed.
    fn run(filter: &Filter, body: impl FnOnce() -> i32) -> Child {
        Self::run_unfiltered(|| match filter.install() {
            Ok(()) => body(),
            Err(_) => Self::INSTALL_FAILED,
        })
    }

    /// Runs `body` in a child process without installing a filter first.
    fn run_unfiltered(body: impl FnOnce() -> i32) -> Child {
        // SAFETY: The child terminates with _exit rather than returning to the test harness.
        // waitpid receives writable status storage and the PID returned by fork;
        // fork, alarm, and _exit take no pointers into Rust memory.
        unsafe {
            let pid = libc::fork();
            assert!(pid >= 0, "fork failed");
            if pid == 0 {
                // A denied exit would leave the child spinning, so cap how long it lives.
                libc::alarm(10);
                let status = body();
                libc::_exit(status);
            }
            let mut status: libc::c_int = 0;
            assert_eq!(libc::waitpid(pid, &mut status, 0), pid, "waitpid failed");
            if libc::WIFSIGNALED(status) {
                Child::Killed(libc::WTERMSIG(status))
            } else {
                Child::Exited(libc::WEXITSTATUS(status))
            }
        }
    }

    /// Calls getpid with explicit arguments and checks whether the filter denied it.
    fn check_getpid(args: [libc::c_ulong; 6], denied: bool) -> bool {
        // SAFETY: getpid ignores these scalar argument registers and accesses no user buffer.
        let ret = unsafe {
            libc::syscall(
                libc::SYS_getpid,
                args[0],
                args[1],
                args[2],
                args[3],
                args[4],
                args[5],
            )
        };
        if denied {
            ret == -1 && Self::errno() == libc::EACCES
        } else {
            ret > 0
        }
    }

    /// Calls the native mmap entry point and checks whether the filter denied it.
    fn check_mmap(args: [libc::c_ulong; 6], denied: bool) -> bool {
        #[cfg(target_pointer_width = "64")]
        let nr = libc::SYS_mmap;
        #[cfg(target_pointer_width = "32")]
        let nr = libc::SYS_mmap2;
        // SAFETY: The arguments are scalar, and the comparison cases use an invalid
        // length or flags so the kernel does not create a mapping.
        let ret = unsafe {
            libc::syscall(nr, args[0], args[1], args[2], args[3], args[4], args[5])
        };
        if denied {
            ret == -1 && Self::errno() == libc::EACCES
        } else {
            ret != -1 || Self::errno() != libc::EACCES
        }
    }

    /// Checks an argument comparison against real syscalls in a filtered child.
    fn assert_cmp(cmp: ArgCmp, cases: &[(libc::c_ulong, bool)]) {
        let arg = cmp.arg as usize;
        let mut filter = Filter::new_native(Action::Allow).unwrap();
        filter
            .add_rule(Action::Errno(libc::EACCES as u16), Syscall::native_mmap(), vec![cmp])
            .unwrap();
        let child = Self::run(&filter, || {
            for (i, &(val, denied)) in cases.iter().enumerate() {
                let mut args = [0; 6];
                args[arg] = val;
                if !Self::check_mmap(args, denied) {
                    return i as i32 + 1;
                }
            }
            0
        });
        assert_eq!(child, Child::Exited(0), "argument {arg}, cases: {cases:?}");
    }
}

#[cfg(target_os = "linux")]
#[test]
fn native_constructor_preserves_default() {
    let mut filter = Filter::new_native(Action::Errno(libc::EACCES as u16)).unwrap();
    filter.add_rule(Action::Allow, Syscall::Exit, vec![]).unwrap();
    filter
        .add_rule(Action::Allow, Syscall::ExitGroup, vec![])
        .unwrap();
    let child = Child::run(&filter, || {
        if !Child::check_getpid([0; 6], true) {
            return 1;
        }
        // SAFETY: getppid takes no arguments and accesses no user buffer.
        let ret = unsafe { libc::syscall(libc::SYS_getppid) };
        if ret != -1 || Child::errno() != libc::EACCES {
            return 2;
        }
        0
    });
    assert_eq!(child, Child::Exited(0));
}

#[cfg(target_os = "linux")]
#[test]
fn empty_architectures_cannot_be_installed() {
    let mut filter = Filter::new(Action::Allow).unwrap();
    filter.on_bad_arch(Action::KillProcess).unwrap();
    assert_eq!(Child::run_unfiltered(|| {
        if matches!(filter.install(), Err(Error::NoArch)) { 0 } else { 1 }
    }), Child::Exited(0));
}

#[cfg(target_os = "linux")]
#[test]
fn invalid_updates_preserve_existing_rules() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter
        .add_rule(Action::Errno(libc::EACCES as u16), Syscall::Getpid, vec![])
        .unwrap();
    assert!(matches!(
        filter.add_arch(Arch::native().unwrap()),
        Err(Error::Check(CheckError::DuplicateArch))
    ));
    for (action, conds) in [
        (Action::Errno(4096), vec![]),
        (Action::Errno(8), vec![ArgCmp::eq(u32::MAX, 0)]),
        (Action::Errno(8), vec![ArgCmp::eq(0, 0), ArgCmp::eq(6, 0)]),
    ] {
        assert!(filter.add_rule(action, Syscall::Getppid, conds).is_err());
    }
    let child = Child::run(&filter, || {
        if !Child::check_getpid([0; 6], true) {
            return 1;
        }
        // SAFETY: getppid takes no arguments and accesses no user buffer.
        if unsafe { libc::syscall(libc::SYS_getppid) } <= 0 {
            return 2;
        }
        0
    });
    assert_eq!(child, Child::Exited(0));
}

#[cfg(target_os = "linux")]
#[test]
fn invalid_bad_arch_preserves_previous_action() {
    let mut filter = Filter::new(Action::Allow).unwrap();
    let absent = if Arch::native().unwrap() == Arch::X86 {
        Arch::Aarch64
    } else {
        Arch::X86
    };
    filter.add_arch(absent).unwrap();
    filter.on_bad_arch(Action::KillProcess).unwrap();
    assert!(matches!(
        filter.on_bad_arch(Action::Errno(4096)),
        Err(Error::Check(CheckError::InvalidErrno(_)))
    ));
    assert_eq!(Child::run(&filter, || 0), Child::Killed(libc::SIGSYS));
}

#[cfg(target_os = "linux")]
#[test]
fn errno_zero_and_maximum_are_enforced() {
    for errno in [0, 4094, 4095] {
        let mut filter = Filter::new_native(Action::Allow).unwrap();
        filter
            .add_rule(Action::Errno(errno), Syscall::Getpid, vec![])
            .unwrap();
        let child = Child::run(&filter, || {
            // SAFETY: getpid takes no arguments and accesses no user buffer.
            let ret = unsafe { libc::syscall(libc::SYS_getpid) };
            if errno == 0 {
                if ret != 0 {
                    return 1;
                }
            } else if ret != -1 || Child::errno() != errno as i32 {
                return 2;
            }
            0
        });
        assert_eq!(child, Child::Exited(0));
    }
}

#[cfg(target_os = "linux")]
#[test]
fn trace_without_tracer_returns_enosys() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter
        .add_rule(Action::Trace(u16::MAX), Syscall::Getpid, vec![])
        .unwrap();
    let child = Child::run(&filter, || {
        // SAFETY: getpid takes no arguments and accesses no user buffer.
        let ret = unsafe { libc::syscall(libc::SYS_getpid) };
        if ret == -1 && Child::errno() == libc::ENOSYS {
            0
        } else {
            1
        }
    });
    assert_eq!(child, Child::Exited(0));
}

#[cfg(target_os = "linux")]
#[test]
fn trap_with_maximum_payload_signals() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter
        .add_rule(Action::Trap(u16::MAX), Syscall::Getpid, vec![])
        .unwrap();
    let child = Child::run(&filter, || {
        // SAFETY: getpid takes no arguments and accesses no user buffer.
        unsafe {
            libc::syscall(libc::SYS_getpid);
        }
        0
    });
    assert_eq!(child, Child::Killed(libc::SIGSYS));
}

#[cfg(target_os = "linux")]
#[test]
fn six_conditions_in_reverse_order_are_conjoined() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    let conds = (0..6).rev().map(|arg| ArgCmp::eq(arg, arg as u64 + 1)).collect();
    filter
        .add_rule(Action::Errno(libc::EACCES as u16), Syscall::native_mmap(), conds)
        .unwrap();
    let child = Child::run(&filter, || {
        let args = [1, 2, 3, 4, 5, 6];
        if !Child::check_mmap(args, true) {
            return 1;
        }
        for arg in 0..6 {
            let mut mismatch = args;
            mismatch[arg] += 1;
            if !Child::check_mmap(mismatch, false) {
                return arg as i32 + 2;
            }
        }
        0
    });
    assert_eq!(child, Child::Exited(0));
}

#[cfg(all(target_os = "linux", target_pointer_width = "64"))]
#[test]
fn equality_checks_both_words() {
    Child::assert_cmp(
        ArgCmp::eq(5, 0x1_0000_0001),
        &[
            (0x1_0000_0001, true),
            (1, false),
            (0x1_0000_0000, false),
            (0x2_0000_0001, false),
        ],
    );
}

#[cfg(all(target_os = "linux", target_pointer_width = "64"))]
#[test]
fn inequality_accepts_either_word_differing() {
    Child::assert_cmp(
        ArgCmp::ne(0, 0x1_0000_0001),
        &[
            (0x1_0000_0001, false),
            (1, true),
            (0x1_0000_0000, true),
            (libc::c_ulong::MAX, true),
        ],
    );
}

#[cfg(all(target_os = "linux", target_pointer_width = "64"))]
#[test]
fn less_than_crosses_word_boundary() {
    Child::assert_cmp(
        ArgCmp::lt(1, 0x1_0000_0001),
        &[
            (0xffff_ffff, true),
            (0x1_0000_0000, true),
            (0x1_0000_0001, false),
            (0x2_0000_0000, false),
        ],
    );
    Child::assert_cmp(ArgCmp::lt(1, 0), &[(0, false), (libc::c_ulong::MAX, false)]);
}

#[cfg(all(target_os = "linux", target_pointer_width = "64"))]
#[test]
fn less_or_equal_includes_boundary() {
    Child::assert_cmp(
        ArgCmp::le(2, 0x1_0000_0000),
        &[
            (0xffff_ffff, true),
            (0x1_0000_0000, true),
            (0x1_0000_0001, false),
            (0x2_0000_0000, false),
        ],
    );
    Child::assert_cmp(ArgCmp::le(2, u64::MAX), &[(0, true), (libc::c_ulong::MAX, true)]);
}

#[cfg(all(target_os = "linux", target_pointer_width = "64"))]
#[test]
fn greater_than_crosses_word_boundary() {
    Child::assert_cmp(
        ArgCmp::gt(3, 0xffff_ffff),
        &[
            (0xffff_fffe, false),
            (0xffff_ffff, false),
            (0x1_0000_0000, true),
            (libc::c_ulong::MAX, true),
        ],
    );
    Child::assert_cmp(
        ArgCmp::gt(3, u64::MAX),
        &[(0, false), (libc::c_ulong::MAX, false)],
    );
}

#[cfg(all(target_os = "linux", target_pointer_width = "64"))]
#[test]
fn greater_or_equal_includes_boundary() {
    Child::assert_cmp(
        ArgCmp::ge(4, 0x1_0000_0000),
        &[
            (0xffff_ffff, false),
            (0x1_0000_0000, true),
            (0x1_0000_0001, true),
            (0x2_0000_0000, true),
        ],
    );
    Child::assert_cmp(ArgCmp::ge(4, 0), &[(0, true), (libc::c_ulong::MAX, true)]);
}

#[cfg(all(target_os = "linux", target_pointer_width = "64"))]
#[test]
fn masked_equality_handles_each_word_independently() {
    Child::assert_cmp(
        ArgCmp::masked_eq(5, 0xf0_0000_000f, 0xa0_0000_0005),
        &[
            (0xa0_0000_0005, true),
            (0xaf_ffff_fff5, true),
            (0xb0_0000_0005, false),
            (0xa0_0000_0006, false),
        ],
    );
    Child::assert_cmp(
        ArgCmp::masked_eq(5, 0xffff_ffff_0000_0000, 0x1_0000_0000),
        &[(0x1_0000_0000, true), (0x1_ffff_ffff, true), (0xffff_ffff, false)],
    );
}

#[cfg(all(target_os = "linux", target_pointer_width = "32"))]
#[test]
fn narrow_architectures_reject_oversized_comparison_values() {
    for make_cmp in [
        ArgCmp::eq as fn(u32, u64) -> ArgCmp,
        ArgCmp::ne, ArgCmp::lt, ArgCmp::le, ArgCmp::gt, ArgCmp::ge,
    ] {
        let mut filter = Filter::new_native(Action::Allow).unwrap();
        assert!(matches!(
            filter.add_rule(Action::Errno(1), Syscall::native_mmap(),
                vec![make_cmp(0, 0x1_8000_0000)]),
            Err(Error::Check(CheckError::InvalidCompareValue { .. })),
        ));
    }
}

#[cfg(all(target_os = "linux", target_pointer_width = "32"))]
#[test]
fn narrow_architectures_reject_oversized_masks() {
    for mask in [0xffff_ffff_0000_0000, 0x1_0000_00ff] {
        let mut filter = Filter::new_native(Action::Allow).unwrap();
        assert!(matches!(
            filter.add_rule(Action::Errno(1), Syscall::native_mmap(),
                vec![ArgCmp::masked_eq(0, mask, 0)]),
            Err(Error::Check(CheckError::InvalidCompareMask { .. })),
        ));
    }
}

#[cfg(target_os = "linux")]
#[test]
fn zero_mask_matches_every_argument() {
    Child::assert_cmp(
        ArgCmp::masked_eq(0, 0, 0),
        &[
            (0, true),
            (1, true),
            (0x8000_0000, true),
            (libc::c_ulong::MAX, true),
        ],
    );
}

#[cfg(target_os = "linux")]
#[test]
fn masked_equality_rejects_value_bits_outside_mask() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    assert!(matches!(
        filter.add_rule(Action::Errno(1), Syscall::native_mmap(),
            vec![ArgCmp::masked_eq(0, 0xf0, 0x1_af)]),
        Err(Error::Check(CheckError::InvalidMaskedValue { arg: 0, mask: 0xf0, value: 0x1_af, .. })),
    ));
}

#[cfg(target_os = "linux")]
#[test]
fn ordering_is_unsigned() {
    let sign = (1 as libc::c_ulong) << (libc::c_ulong::BITS - 1);
    let policy_sign = 1u64 << (libc::c_ulong::BITS - 1);
    Child::assert_cmp(
        ArgCmp::lt(0, policy_sign),
        &[
            (0, true),
            (sign - 1, true),
            (sign, false),
            (libc::c_ulong::MAX, false),
        ],
    );
    Child::assert_cmp(
        ArgCmp::gt(0, policy_sign),
        &[
            (0, false),
            (sign - 1, false),
            (sign, false),
            (libc::c_ulong::MAX, true),
        ],
    );
}

#[cfg(all(target_os = "linux", target_arch = "x86_64", target_pointer_width = "64"))]
#[test]
fn x86_64_unmatched_syscall_numbers_select_abi_default() {
    let mut filter = Filter::new_native(Action::Errno(libc::EACCES as u16)).unwrap();
    filter.on_bad_arch(Action::Errno(libc::EPERM as u16)).unwrap();
    filter.add_rule(Action::Allow, Syscall::Exit, vec![]).unwrap();
    filter.add_rule(Action::Allow, Syscall::ExitGroup, vec![]).unwrap();
    let child = Child::run(&filter, || {
        for (i, nr) in [
            -1,
            -2,
            i32::MIN,
            0x3fff_ffff,
            0x4000_0000,
            i32::MAX,
        ]
        .iter()
        .enumerate()
        {
            // SAFETY: These numbers are invalid or select x32 read. The latter receives
            // an invalid descriptor and a null, zero-length buffer, so it cannot write memory.
            let ret = unsafe {
                libc::syscall(
                    *nr as libc::c_long,
                    -1 as libc::c_long,
                    0 as libc::c_ulong,
                    0 as libc::c_ulong,
                )
            };
            let expected = if *nr != -1 && *nr & 0x4000_0000 != 0 {
                libc::EPERM
            } else {
                libc::EACCES
            };
            if ret != -1 || Child::errno() != expected {
                return i as i32 + 1;
            }
        }
        0
    });
    assert_eq!(child, Child::Exited(0));
}

#[cfg(all(target_os = "linux", target_arch = "x86_64", target_pointer_width = "64"))]
#[test]
fn x86_64_skip_rule_matches_minus_one() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter.on_bad_arch(Action::Errno(libc::EPERM as u16)).unwrap();
    filter
        .add_rule(Action::Errno(libc::EACCES as u16), Syscall::Skip, vec![])
        .unwrap();
    let child = Child::run(&filter, || {
        // SAFETY: The filter returns EACCES before the invalid syscall reaches the kernel.
        let ret = unsafe { libc::syscall(-1 as libc::c_long) };
        if ret == -1 && Child::errno() == libc::EACCES {
            0
        } else {
            1
        }
    });
    assert_eq!(child, Child::Exited(0));
}

#[cfg(all(target_os = "linux", target_arch = "x86"))]
#[test]
fn socket_rule_covers_direct_and_multiplexed_calls() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter
        .add_rule(Action::Errno(libc::EACCES as u16), Syscall::Socket, vec![])
        .unwrap();
    // SAFETY: The socketcall argument arrays stay alive during each syscall. Socket creation
    // takes only scalars; bind receives an invalid descriptor and a null, zero-length address.
    let child = Child::run(&filter, || unsafe {
        let args = [0 as libc::c_ulong; 3];
        if libc::syscall(libc::SYS_socket, args[0], args[1], args[2]) != -1 || Child::errno() != libc::EACCES
        {
            return 1;
        }
        if libc::syscall(libc::SYS_socketcall, 1 as libc::c_ulong, args.as_ptr()) != -1
            || Child::errno() != libc::EACCES
        {
            return 2;
        }
        let bind_args = [libc::c_ulong::MAX, 0, 0];
        if libc::syscall(libc::SYS_socketcall, 2 as libc::c_ulong, bind_args.as_ptr()) != -1
            || Child::errno() != libc::EBADF
        {
            return 3;
        }
        0
    });
    assert_eq!(child, Child::Exited(0));
}

#[cfg(all(target_os = "linux", target_arch = "x86"))]
#[test]
fn conditional_socket_rule_exact_only_covers_direct_call() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter
        .add_rule_exact(
            Action::Errno(libc::EACCES as u16),
            Syscall::Socket,
            vec![ArgCmp::eq(0, 1)],
        )
        .unwrap();
    // SAFETY: Socket creation takes only scalar arguments. The socketcall array contains
    // those same arguments and stays alive while the kernel reads it.
    let child = Child::run(&filter, || unsafe {
        if libc::syscall(
            libc::SYS_socket,
            1 as libc::c_ulong,
            0 as libc::c_ulong,
            0 as libc::c_ulong,
        ) != -1
            || Child::errno() != libc::EACCES
        {
            return 1;
        }
        // A zero socket type fails in the kernel if the filter lets it through.
        let args = [0 as libc::c_ulong; 3];
        if libc::syscall(libc::SYS_socket, args[0], args[1], args[2]) != -1 || Child::errno() == libc::EACCES
        {
            return 2;
        }
        if libc::syscall(libc::SYS_socketcall, 1 as libc::c_ulong, args.as_ptr()) != -1
            || Child::errno() == libc::EACCES
        {
            return 3;
        }
        0
    });
    assert_eq!(child, Child::Exited(0));
}

#[cfg(all(target_os = "linux", target_arch = "x86"))]
#[test]
fn exact_socket_rule_excludes_socketcall_without_conditions() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter
        .add_rule_exact(Action::Errno(libc::EACCES as u16), Syscall::Socket, vec![])
        .unwrap();
    // SAFETY: Socket creation uses scalar arguments, and the socketcall array stays alive.
    let child = Child::run(&filter, || unsafe {
        if libc::syscall(libc::SYS_socket, 1 as libc::c_ulong, 0, 0) != -1
            || Child::errno() != libc::EACCES
        {
            return 1;
        }
        let args = [0 as libc::c_ulong; 3];
        if libc::syscall(libc::SYS_socketcall, 1 as libc::c_ulong, args.as_ptr()) != -1
            || Child::errno() == libc::EACCES
        {
            return 2;
        }
        0
    });
    assert_eq!(child, Child::Exited(0));
}

#[cfg(all(target_os = "linux", target_arch = "x86"))]
#[test]
fn ipc_rule_ignores_selector_version_bits() {
    // The i386 semget number in `arch/x86/entry/syscalls/syscall_32.tbl`.
    let semget: libc::c_long = 393;
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter
        .add_rule(Action::Errno(libc::EACCES as u16), Syscall::Semget, vec![])
        .unwrap();
    // SAFETY: The direct call and both IPC selectors select semget, which takes scalar
    // arguments and does not access a user buffer.
    let child = Child::run(&filter, || unsafe {
        if libc::syscall(
            semget,
            0 as libc::c_ulong,
            0 as libc::c_ulong,
            0 as libc::c_ulong,
        ) != -1
            || Child::errno() != libc::EACCES
        {
            return 1;
        }
        for (i, selector) in [2, 0x1_0002].iter().enumerate() {
            // Zero semaphores cannot create an IPC object.
            let ret = libc::syscall(
                libc::SYS_ipc,
                *selector as libc::c_ulong,
                0 as libc::c_ulong,
                0 as libc::c_ulong,
                0 as libc::c_ulong,
                0 as libc::c_ulong,
            );
            if ret != -1 || Child::errno() != libc::EACCES {
                return i as i32 + 2;
            }
        }
        0
    });
    assert_eq!(child, Child::Exited(0));
}

#[cfg(all(target_os = "linux", target_arch = "x86"))]
#[test]
fn exact_ipc_rule_excludes_multiplexed_call() {
    let semget: libc::c_long = 393;
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter
        .add_rule_exact(Action::Errno(libc::EACCES as u16), Syscall::Semget, vec![])
        .unwrap();
    // SAFETY: Both calls select semget, which uses scalar arguments only.
    let child = Child::run(&filter, || unsafe {
        if libc::syscall(semget, 0 as libc::c_ulong, 0, 0) != -1
            || Child::errno() != libc::EACCES
        {
            return 1;
        }
        if libc::syscall(libc::SYS_ipc, 0x1_0002 as libc::c_ulong, 0, 0, 0, 0) != -1
            || Child::errno() == libc::EACCES
        {
            return 2;
        }
        0
    });
    assert_eq!(child, Child::Exited(0));
}

#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
#[test]
fn unavailable_syscall_does_not_alias_another_number() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter.add_arch(Arch::X86_64).unwrap();
    filter
        .add_rule(Action::Errno(libc::EACCES as u16), Syscall::Open, vec![])
        .unwrap();
    // SAFETY: io_submit receives an invalid context and zero requests. openat receives
    // a null pathname, which the kernel rejects with EFAULT without accessing Rust memory.
    let child = Child::run(&filter, || unsafe {
        // The x86_64 open number is io_submit on aarch64.
        if libc::syscall(
            libc::SYS_io_submit,
            0 as libc::c_ulong,
            0 as libc::c_ulong,
            0 as libc::c_ulong,
        ) != -1
            || Child::errno() == libc::EACCES
        {
            return 1;
        }
        if libc::syscall(
            libc::SYS_openat,
            -1 as libc::c_long,
            0 as libc::c_ulong,
            0 as libc::c_ulong,
            0 as libc::c_ulong,
        ) != -1
            || Child::errno() != libc::EFAULT
        {
            return 2;
        }
        0
    });
    assert_eq!(child, Child::Exited(0));
}

#[cfg(target_os = "linux")]
#[test]
fn long_rule_chains_preserve_matches_and_fallthrough() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    for val in 0..100 {
        filter
            .add_rule(
                Action::Errno(libc::EACCES as u16),
                Syscall::native_mmap(),
                vec![ArgCmp::eq(0, val)],
            )
            .unwrap();
    }
    assert!(filter.policy.to_cbpf().ok().unwrap().instrs.len() > 255);
    let child = Child::run(&filter, || {
        for (i, val) in [0, 50, 99, 100].iter().enumerate() {
            if !Child::check_mmap([*val, 0, 0, 0, 0, 0], *val < 100) {
                return i as i32 + 1;
            }
        }
        // SAFETY: getppid takes no arguments and accesses no user buffer.
        if unsafe { libc::syscall(libc::SYS_getppid) } <= 0 {
            return 5;
        }
        0
    });
    assert_eq!(child, Child::Exited(0));
}

/// A filter with no rules and an `SCMP_ACT_ALLOW` default lets the child run on.
#[cfg(target_os = "linux")]
#[test]
fn allow_all() {
    let filter = Filter::new_native(Action::Allow).unwrap();
    // SAFETY: getpid takes no arguments and accesses no user buffer.
    let child = Child::run(&filter, || unsafe {
        if libc::syscall(libc::SYS_getpid) > 0 {
            0
        } else {
            1
        }
    });
    assert_eq!(child, Child::Exited(0));
}

/// An `SCMP_ACT_ERRNO` rule fails its own syscall and no other.
#[cfg(target_os = "linux")]
#[test]
fn errno_on_getpid() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter
        .add_rule(Action::Errno(libc::EPERM as u16), Syscall::Getpid, vec![])
        .unwrap();
    // SAFETY: getpid and getppid take no arguments and access no user buffer.
    let child = Child::run(&filter, || unsafe {
        if libc::syscall(libc::SYS_getpid) != -1 {
            return 1;
        }
        if Child::errno() != libc::EPERM {
            return 2;
        }
        if libc::syscall(libc::SYS_getppid) <= 0 {
            return 3;
        }
        0
    });
    assert_eq!(child, Child::Exited(0));
}

/// An argument test narrows a rule to the calls that pass it.
#[cfg(target_os = "linux")]
#[test]
fn errno_on_first_argument() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    let conds = vec![ArgCmp::eq(0, 42)];
    filter
        .add_rule(Action::Errno(libc::EPERM as u16), Syscall::Lseek, conds)
        .unwrap();
    let child = Child::run(&filter, || {
        // `lseek` on a descriptor nothing opened, which the kernel refuses with EBADF.
        // SAFETY: lseek takes scalar arguments of the syscall ABI's word size, with no pointers.
        let lseek = |fd: libc::c_long, offset: libc::c_long| unsafe {
            libc::syscall(libc::SYS_lseek, fd, offset, libc::SEEK_SET as libc::c_long)
        };
        if lseek(42, 0) != -1 {
            return 1;
        }
        if Child::errno() != libc::EPERM {
            return 2;
        }
        if lseek(43, 0) != -1 {
            return 3;
        }
        if Child::errno() != libc::EBADF {
            return 4;
        }
        0
    });
    assert_eq!(child, Child::Exited(0));
}

/// An `SCMP_ACT_KILL_PROCESS` rule takes the child down with SIGSYS.
#[cfg(target_os = "linux")]
#[test]
fn kill_process_on_getppid() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter
        .add_rule(Action::KillProcess, Syscall::Getppid, vec![])
        .unwrap();
    // SAFETY: getppid takes no arguments and accesses no user buffer.
    let child = Child::run(&filter, || unsafe {
        libc::syscall(libc::SYS_getppid);
        0
    });
    assert_eq!(child, Child::Killed(libc::SIGSYS));
}

/// An argument test on a 64-bit architecture looks at both words of the argument.
#[cfg(target_pointer_width = "64")]
#[cfg(target_os = "linux")]
#[test]
fn errno_on_high_word_of_argument() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    let conds = vec![ArgCmp::eq(1, 0x1_0000_0000)];
    filter
        .add_rule(Action::Errno(libc::EPERM as u16), Syscall::Lseek, conds)
        .unwrap();
    let child = Child::run(&filter, || {
        // `lseek` on a descriptor nothing opened, which the kernel refuses with EBADF.
        // SAFETY: lseek takes scalar arguments of the syscall ABI's word size, with no pointers.
        let lseek = |fd: libc::c_long, offset: libc::c_long| unsafe {
            libc::syscall(libc::SYS_lseek, fd, offset, libc::SEEK_SET as libc::c_long)
        };
        if lseek(43, 0x1_0000_0000) != -1 {
            return 1;
        }
        if Child::errno() != libc::EPERM {
            return 2;
        }
        if lseek(43, 1) != -1 {
            return 3;
        }
        if Child::errno() != libc::EBADF {
            return 4;
        }
        0
    });
    assert_eq!(child, Child::Exited(0));
}

/// An event from an architecture the filter leaves out takes `act_bad_arch`.
#[cfg(target_os = "linux")]
#[test]
fn bad_arch_kills() {
    let absent = if Arch::native().unwrap() == Arch::X86 {
        Arch::Aarch64
    } else {
        Arch::X86
    };
    let mut filter = Filter::new(Action::Allow).ok().unwrap();
    filter.add_arch(absent).ok().unwrap();
    filter.on_bad_arch(Action::KillProcess).ok().unwrap();
    // SAFETY: getpid takes no arguments and accesses no user buffer.
    let child = Child::run(&filter, || unsafe {
        libc::syscall(libc::SYS_getpid);
        0
    });
    assert_eq!(child, Child::Killed(libc::SIGSYS));
}

/// Errno payloads above Linux's maximum are rejected rather than clamped.
#[test]
fn errno_out_of_range() {
    assert!(Filter::new(Action::Errno(Action::MAX_ERRNO as u16 + 1)).is_err());
    assert!(Filter::new(Action::Errno(Action::MAX_ERRNO as u16)).is_ok());
}

/// The same architecture twice is turned down.
#[test]
fn duplicate_arch() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    assert!(filter.add_arch(Arch::native().unwrap()).is_err());
}

/// A rule that repeats the default action is allowed.
#[test]
fn rule_repeats_default() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    assert!(filter
        .add_rule(Action::Allow, Syscall::Getpid, vec![])
        .is_ok());
}

/// Multiple tests of one argument in a single rule compile together.
#[test]
fn repeated_argument_conditions_compile() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    let conds = vec![ArgCmp::eq(1, 0), ArgCmp::ne(1, 1)];
    filter.add_rule(Action::Errno(1), Syscall::Lseek, conds).unwrap();
    assert!(filter.policy.to_cbpf().is_ok());
}

/// An argument the architecture does not have is turned down.
#[test]
fn argument_out_of_range() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    let conds = vec![ArgCmp::eq(6, 0)];
    assert!(matches!(
        filter.add_rule(Action::Errno(1), Syscall::Lseek, conds),
        Err(Error::Check(CheckError::InvalidArg { given: 6, total: 3, syscall: Syscall::Lseek })),
    ));
}

#[test]
fn rule_checks_condition_indices() {
    let archs = vec![Arch::native().unwrap()];
    let syscall = Syscall::native_mmap();
    let rule = |conds| Rule {
        action: Action::Allow,
        syscall,
        conds,
        no_mux: false,
    };
    assert!(rule(vec![]).check(archs.as_slice()).is_ok());
    assert!(rule((0..6).rev().map(|arg| ArgCmp::eq(arg, 0)).collect())
        .check(archs.as_slice())
        .is_ok());
    assert!(rule((0..7).map(|arg| ArgCmp::eq(arg % 6, 0)).collect())
        .check(archs.as_slice())
        .is_ok());
    assert!(matches!(
        rule((0..7).map(|arg| ArgCmp::eq(arg, 0)).collect()).check(archs.as_slice()),
        Err(CheckError::InvalidArg { given: 6, total: 6, syscall: s }) if s == syscall,
    ));
    assert!(matches!(
        rule(vec![ArgCmp::eq(u32::MAX, 0)]).check(archs.as_slice()),
        Err(CheckError::InvalidArg { given: u32::MAX, total: 6, syscall: s }) if s == syscall,
    ));
    assert!(rule(vec![ArgCmp::eq(5, 0), ArgCmp::eq(0, 0), ArgCmp::ne(5, 1)])
        .check(archs.as_slice())
        .is_ok());
}

#[test]
fn action_checks_return_validation_errors() {
    for action in [
        Action::KillProcess,
        Action::KillThread,
        Action::Allow,
        Action::Log,
        Action::Notify,
        Action::Errno(0),
        Action::Errno(4094),
        Action::Errno(4095),
        Action::Trace(u16::MAX),
        Action::Trap(u16::MAX),
    ] {
        assert!(action.check().is_ok());
    }
    for errno in [4096, u16::MAX] {
        assert!(matches!(
            Action::Errno(errno).check(),
            Err(CheckError::InvalidErrno(_))
        ));
    }
}

#[test]
fn rule_checks_propagate_validation_errors() {
    let archs = vec![Arch::native().unwrap()];
    let syscall = Syscall::native_mmap();
    let rule = |action, conds| Rule {
        action,
        syscall,
        conds,
        no_mux: false,
    };
    assert!(rule(Action::Errno(1), vec![]).check(archs.as_slice()).is_ok());
    assert!(matches!(
        rule(Action::Errno(4096), vec![]).check(archs.as_slice()),
        Err(CheckError::InvalidErrno(_))
    ));
    assert!(Filter::new_native(Action::Allow)
        .unwrap()
        .add_rule(Action::Allow, Syscall::Getpid, vec![])
        .is_ok());
    assert!(matches!(
        rule(Action::Errno(1), (0..7).map(|arg| ArgCmp::eq(arg, 0)).collect())
            .check(archs.as_slice()),
        Err(CheckError::InvalidArg { given: 6, total: 6, syscall: s }) if s == syscall,
    ));
    assert!(matches!(
        rule(Action::Errno(1), vec![ArgCmp::eq(6, 0)]).check(archs.as_slice()),
        Err(CheckError::InvalidArg { given: 6, total: 6, syscall: s }) if s == syscall,
    ));
    assert!(rule(Action::Errno(1), vec![ArgCmp::eq(1, 0), ArgCmp::ne(1, 1)])
        .check(archs.as_slice())
        .is_ok());
}

#[test]
fn skip_rule_is_allowed() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    assert!(filter.add_rule(Action::Errno(1), Syscall::Skip, vec![]).is_ok());
    assert!(matches!(
        filter.add_rule(Action::Errno(1), Syscall::Skip, vec![ArgCmp::eq(0, 0)]),
        Err(Error::Check(CheckError::InvalidArg { given: 0, total: 0, syscall: Syscall::Skip })),
    ));
}

#[test]
fn zero_argument_syscall_rejects_conditions() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    assert!(matches!(
        filter.add_rule(Action::Errno(1), Syscall::Getpid, vec![ArgCmp::eq(0, 0)]),
        Err(Error::Check(CheckError::InvalidArg { given: 0, total: 0, syscall: Syscall::Getpid })),
    ));
}

#[test]
fn typed_condition_errors_report_the_argument_type() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    assert!(matches!(
        filter.add_rule(Action::Errno(1), Syscall::Fchmodat, vec![ArgCmp::lt(1, 0)]),
        Err(Error::Check(CheckError::UnsupportedCompare { arg: 1, ty: crate::PrimType::Ptr, .. })),
    ));
    assert!(matches!(
        filter.add_rule(Action::Errno(1), Syscall::Fchmod, vec![ArgCmp::eq(1, 0x1_0000)]),
        Err(Error::Check(CheckError::InvalidCompareValue { arg: 1, ty: crate::PrimType::U(16), .. })),
    ));
    assert!(matches!(
        filter.add_rule(Action::Errno(1), Syscall::Fchmod,
            vec![ArgCmp::masked_eq(1, 0x1_0000, 0)]),
        Err(Error::Check(CheckError::InvalidCompareMask { arg: 1, ty: crate::PrimType::U(16), .. })),
    ));
}

#[test]
fn adding_architecture_rejects_signature_conflicts() {
    let mut filter = Filter::new(Action::Allow).unwrap();
    filter.add_arch(Arch::X86).unwrap();
    filter.add_rule(Action::Errno(1), Syscall::Chown, vec![ArgCmp::eq(1, 1)]).unwrap();
    let before = filter.clone();
    assert!(matches!(filter.add_arch(Arch::X86_64), Err(Error::Check(CheckError::IncompatSigs))));
    assert_eq!(filter, before);

    let mut compatible = Filter::new(Action::Allow).unwrap();
    compatible.add_arch(Arch::X86_64).unwrap();
    compatible.add_rule(Action::Errno(1), Syscall::Lseek,
        vec![ArgCmp::eq(1, 0)]).unwrap();
    compatible.add_arch(Arch::Aarch64).unwrap();
    assert!(compatible.policy.to_cbpf().is_ok());
}

#[test]
fn split_arguments_use_adjacent_or_aligned_slots() {
    for (arch, expected) in [
        (Arch::X86, vec![40, 48]),
        (Arch::Arm, vec![48, 56]),
    ] {
        let mut filter = Filter::new(Action::Allow).unwrap();
        filter.add_arch(arch).unwrap();
        filter.add_rule(Action::Errno(1), Syscall::Pread64,
            vec![ArgCmp::eq(3, 0x1_0000_0000)]).unwrap();
        let program = filter.policy.to_cbpf().unwrap();
        let mut loads: Vec<u32> = program.instrs.iter().filter_map(|instr| match instr {
            Instr::LdAbs(k) if *k >= 16 => Some(*k),
            _ => None,
        }).collect();
        loads.sort_unstable();
        assert_eq!(loads, expected, "architecture: {arch:?}");
    }
}

#[test]
fn signed_and_narrow_comparisons_add_one_alu_instruction() {
    for arch in [Arch::X86, Arch::X86_64] {
        let mut filter = Filter::new(Action::Allow).unwrap();
        filter.add_arch(arch).unwrap();
        filter.add_rule(Action::Errno(1), Syscall::Lseek,
            vec![ArgCmp::lt(1, u64::MAX)]).unwrap();
        let program = filter.policy.to_cbpf().unwrap();
        assert_eq!(program.instrs.iter().filter(|instr|
            **instr == Instr::Alu(AluOp::Xor, Src::K(0x8000_0000))).count(), 1);
    }

    let mut filter = Filter::new(Action::Allow).unwrap();
    filter.add_arch(Arch::Aarch64).unwrap();
    filter.add_rule(Action::Errno(1), Syscall::Fchmod,
        vec![ArgCmp::eq(1, 0xFFFF)]).unwrap();
    let program = filter.policy.to_cbpf().unwrap();
    assert_eq!(program.instrs.iter().filter(|instr|
        **instr == Instr::Alu(AluOp::And, Src::K(0xFFFF))).count(), 1);
}

#[test]
fn mux_rules_require_exact_mode_for_argument_conditions() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    for syscall in [Syscall::Socket, Syscall::Semget] {
        let conds = vec![ArgCmp::eq(0, 1)];
        let rule_count = filter.policy.rules.len();
        assert!(matches!(
            filter.add_rule(Action::Errno(1), syscall, conds.clone()),
            Err(Error::Check(CheckError::InvalidMuxConditions))
        ));
        assert_eq!(filter.policy.rules.len(), rule_count);
        filter.add_rule_exact(Action::Errno(1), syscall, conds).unwrap();
        assert!(filter.policy.rules.last().unwrap().no_mux);
    }
    filter.add_rule(Action::Errno(1), Syscall::Socket, vec![]).unwrap();
    assert!(!filter.policy.rules.last().unwrap().no_mux);
}
