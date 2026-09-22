//! Tests of filter construction and native seccomp enforcement.

use crate::api::{Error, Filter};
use crate::spec::policy::{Action, Arch, ArgCmp, Rule, Syscall};

#[test]
fn native_constructor_adds_only_native() {
    let mut filter = Filter::new_native(Action::Errno(7)).unwrap();
    let native = Arch::native().unwrap();
    assert!(matches!(filter.add_arch(native), Err(Error::DuplicateArch)));
    for arch in [Arch::X86, Arch::X86_64, Arch::Arm, Arch::Aarch64] {
        if arch != native {
            filter.add_arch(arch).unwrap();
        }
    }
    assert!(matches!(
        Filter::new_native(Action::Errno(4095)),
        Err(Error::InvalidErrno)
    ));
}

#[test]
fn seven_conditions_compile() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    let conds = (0..7).map(|arg| ArgCmp::eq(arg % 6, 0)).collect();
    filter.add_rule(Action::Errno(1), Syscall::Getpid, conds).unwrap();
    assert!(filter.to_cbpf().is_ok());
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
        Action::Trace(u16::MAX),
        Action::Trap(u16::MAX),
    ] {
        let mut filter = Filter::new_native(Action::Allow).unwrap();
        filter.add_rule(action, Syscall::Getpid, vec![]).unwrap();
    }
    for errno in [4095, 4096, u16::MAX] {
        assert!(matches!(
            Filter::new(Action::Errno(errno)),
            Err(Error::InvalidErrno)
        ));
    }
}

#[test]
fn oversized_program_compiles() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    for val in 0..1000 {
        filter
            .add_rule(Action::Errno(13), Syscall::Getpid, vec![ArgCmp::eq(0, val)])
            .unwrap();
    }
    let program = filter.to_cbpf().unwrap();
    assert!(program.instrs.len() > 4096);
    #[cfg(target_os = "linux")]
    assert_eq!(Child::run_unfiltered(|| {
        if !matches!(filter.install(), Err(Error::FilterTooLarge)) {
            return 1;
        }
        if !matches!(program.install(&filter), Err(Error::FilterTooLarge)) {
            return 2;
        }
        0
    }), Child::Exited(0));
}

#[cfg(target_os = "linux")]
#[test]
fn installation_checks_instruction_limit_before_side_effects() {
    use crate::spec::cbpf::{Instr, Program, RetVal};

    // Also check a length that would wrap to 1 when cast to sock_fprog.len.
    for len in [4096, 4097, 65537] {
        let child = Child::run_unfiltered(|| {
            let filter = Filter::new(Action::Allow).unwrap();
            let program = Program {
                instrs: (0..len)
                    .map(|_| Instr::Ret(RetVal::K(Action::Allow.to_ret())))
                    .collect(),
            };
            let before = unsafe { libc::prctl(libc::PR_GET_NO_NEW_PRIVS, 0, 0, 0, 0) };
            if before < 0 {
                return 1;
            }
            let result = program.install(&filter);
            if len == 4096 {
                return if result.is_ok() { 0 } else { 2 };
            }
            if !matches!(result, Err(Error::FilterTooLarge)) {
                return 3;
            }
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

    /// Checks an argument comparison against real syscalls in a filtered child.
    fn assert_cmp(cmp: ArgCmp, cases: &[(libc::c_ulong, bool)]) {
        let arg = cmp.arg as usize;
        let mut filter = Filter::new_native(Action::Allow).unwrap();
        filter
            .add_rule(Action::Errno(libc::EACCES as u16), Syscall::Getpid, vec![cmp])
            .unwrap();
        let child = Self::run(&filter, || {
            for (i, &(val, denied)) in cases.iter().enumerate() {
                let mut args = [0; 6];
                args[arg] = val;
                if !Self::check_getpid(args, denied) {
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
fn empty_architectures_always_take_bad_arch() {
    let mut filter = Filter::new(Action::Allow).unwrap();
    filter.on_bad_arch(Action::KillProcess).unwrap();
    assert_eq!(Child::run(&filter, || 0), Child::Killed(libc::SIGSYS));
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
        Err(Error::DuplicateArch)
    ));
    for (action, conds) in [
        (Action::Errno(4095), vec![]),
        (Action::Errno(8), vec![ArgCmp::eq(u32::MAX, 0)]),
        (Action::Errno(8), vec![ArgCmp::eq(0, 0), ArgCmp::eq(6, 0)]),
    ] {
        assert!(filter.add_rule(action, Syscall::Getppid, conds).is_err());
    }
    let child = Child::run(&filter, || {
        if !Child::check_getpid([0; 6], true) {
            return 1;
        }
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
    filter.on_bad_arch(Action::KillProcess).unwrap();
    assert!(matches!(
        filter.on_bad_arch(Action::Errno(4095)),
        Err(Error::InvalidErrno)
    ));
    assert_eq!(Child::run(&filter, || 0), Child::Killed(libc::SIGSYS));
}

#[cfg(target_os = "linux")]
#[test]
fn errno_zero_and_maximum_are_enforced() {
    for errno in [0, 4094] {
        let mut filter = Filter::new_native(Action::Allow).unwrap();
        filter
            .add_rule(Action::Errno(errno), Syscall::Getpid, vec![])
            .unwrap();
        let child = Child::run(&filter, || {
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
        .add_rule(Action::Errno(libc::EACCES as u16), Syscall::Getpid, conds)
        .unwrap();
    let child = Child::run(&filter, || {
        let args = [1, 2, 3, 4, 5, 6];
        if !Child::check_getpid(args, true) {
            return 1;
        }
        for arg in 0..6 {
            let mut mismatch = args;
            mismatch[arg] += 1;
            if !Child::check_getpid(mismatch, false) {
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
fn narrow_architectures_truncate_comparison_values() {
    for (make_cmp, below, equal, above) in [
        (ArgCmp::eq as fn(u32, u64) -> ArgCmp, false, true, false),
        (ArgCmp::ne, true, false, true),
        (ArgCmp::lt, true, false, false),
        (ArgCmp::le, true, true, false),
        (ArgCmp::gt, false, false, true),
        (ArgCmp::ge, false, true, true),
    ] {
        Child::assert_cmp(
            make_cmp(0, 0x1_8000_0000),
            &[(0x7fff_ffff, below), (0x8000_0000, equal), (0x8000_0001, above)],
        );
    }
}

#[cfg(all(target_os = "linux", target_pointer_width = "32"))]
#[test]
fn narrow_architectures_truncate_masks() {
    Child::assert_cmp(
        ArgCmp::masked_eq(0, 0xffff_ffff_0000_0000, u64::MAX),
        &[(0, true), (libc::c_ulong::MAX, true)],
    );
    Child::assert_cmp(
        ArgCmp::masked_eq(0, 0x1_0000_00ff, 0x2_0000_002a),
        &[(42, true), (0xffff_ff2a, true), (43, false)],
    );
}

#[cfg(target_os = "linux")]
#[test]
fn zero_mask_matches_every_argument() {
    Child::assert_cmp(
        ArgCmp::masked_eq(0, 0, u64::MAX),
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
fn masked_equality_ignores_value_bits_outside_mask() {
    Child::assert_cmp(
        ArgCmp::masked_eq(0, 0xf0, 0x1_af),
        &[
            (0xa0, true),
            (0xaf, true),
            (libc::c_ulong::MAX - 0x50, true),
            (0xb0, false),
        ],
    );
}

#[cfg(target_os = "linux")]
#[test]
fn ordering_is_unsigned() {
    let sign = (1 as libc::c_ulong) << (libc::c_ulong::BITS - 1);
    Child::assert_cmp(
        ArgCmp::lt(0, sign as u64),
        &[
            (0, true),
            (sign - 1, true),
            (sign, false),
            (libc::c_ulong::MAX, false),
        ],
    );
    Child::assert_cmp(
        ArgCmp::gt(0, sign as u64),
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
fn x86_64_unmatched_syscall_numbers_take_default() {
    let mut filter = Filter::new_native(Action::Errno(libc::EACCES as u16)).unwrap();
    filter.on_bad_arch(Action::KillProcess).unwrap();
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
            let ret = unsafe {
                libc::syscall(
                    *nr as libc::c_long,
                    -1 as libc::c_long,
                    0 as libc::c_ulong,
                    0 as libc::c_ulong,
                )
            };
            if ret != -1 || Child::errno() != libc::EACCES {
                return i as i32 + 1;
            }
        }
        0
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
fn conditional_socket_rule_only_covers_direct_call() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter
        .add_rule(
            Action::Errno(libc::EACCES as u16),
            Syscall::Socket,
            vec![ArgCmp::eq(0, 1)],
        )
        .unwrap();
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
fn ipc_rule_checks_the_full_low_word_of_selector() {
    // The i386 semget number in `arch/x86/entry/syscalls/syscall_32.tbl`.
    let semget: libc::c_long = 393;
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    filter
        .add_rule(Action::Errno(libc::EACCES as u16), Syscall::Semget, vec![])
        .unwrap();
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
            let expected = if *selector == 2 {
                libc::EACCES
            } else {
                libc::EINVAL
            };
            if ret != -1 || Child::errno() != expected {
                return i as i32 + 2;
            }
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
                Syscall::Getpid,
                vec![ArgCmp::eq(0, val)],
            )
            .unwrap();
    }
    assert!(filter.to_cbpf().ok().unwrap().instrs.len() > 255);
    let child = Child::run(&filter, || {
        for (i, val) in [0, 50, 99, 100].iter().enumerate() {
            if !Child::check_getpid([*val, 0, 0, 0, 0, 0], *val < 100) {
                return i as i32 + 1;
            }
        }
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
    let child = Child::run(&filter, || unsafe {
        libc::syscall(libc::SYS_getpid);
        0
    });
    assert_eq!(child, Child::Killed(libc::SIGSYS));
}

/// An errno the kernel has no room for is turned down.
#[test]
fn errno_out_of_range() {
    assert!(Filter::new(Action::Errno(Action::MAX_ERRNO as u16)).is_err());
    assert!(Filter::new(Action::Errno(Action::MAX_ERRNO as u16 - 1)).is_ok());
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
    assert!(filter.to_cbpf().is_ok());
}

/// An argument the architecture does not have is turned down.
#[test]
fn argument_out_of_range() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    let conds = vec![ArgCmp::eq(6, 0)];
    assert!(matches!(
        filter.add_rule(Action::Errno(1), Syscall::Lseek, conds),
        Err(Error::InvalidArg(6)),
    ));
}

#[test]
fn rule_checks_condition_indices() {
    let rule = |conds| Rule {
        action: Action::Allow,
        syscall: Syscall::Getpid,
        conds,
        exact: false,
    };
    assert!(rule(vec![]).check().is_ok());
    assert!(rule((0..6).rev().map(|arg| ArgCmp::eq(arg, 0)).collect())
        .check()
        .is_ok());
    assert!(rule((0..7).map(|arg| ArgCmp::eq(arg % 6, 0)).collect())
        .check()
        .is_ok());
    assert!(matches!(
        rule((0..7).map(|arg| ArgCmp::eq(arg, 0)).collect()).check(),
        Err(Error::InvalidArg(6)),
    ));
    assert!(matches!(
        rule(vec![ArgCmp::eq(u32::MAX, 0)]).check(),
        Err(Error::InvalidArg(u32::MAX)),
    ));
    assert!(rule(vec![ArgCmp::eq(5, 0), ArgCmp::eq(0, 0), ArgCmp::ne(5, 1)])
        .check()
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
        Action::Trace(u16::MAX),
        Action::Trap(u16::MAX),
    ] {
        assert!(action.check().is_ok());
    }
    for errno in [4095, 4096, u16::MAX] {
        assert!(matches!(
            Action::Errno(errno).check(),
            Err(Error::InvalidErrno)
        ));
    }
}

#[test]
fn rule_checks_propagate_validation_errors() {
    let rule = |action, conds| Rule {
        action,
        syscall: Syscall::Getpid,
        conds,
        exact: false,
    };
    assert!(rule(Action::Errno(1), vec![]).check().is_ok());
    assert!(matches!(
        rule(Action::Errno(4095), vec![]).check(),
        Err(Error::InvalidErrno)
    ));
    assert!(Filter::new_native(Action::Allow)
        .unwrap()
        .add_rule(Action::Allow, Syscall::Getpid, vec![])
        .is_ok());
    assert!(matches!(
        rule(Action::Errno(1), (0..7).map(|arg| ArgCmp::eq(arg, 0)).collect()).check(),
        Err(Error::InvalidArg(6)),
    ));
    assert!(matches!(
        rule(Action::Errno(1), vec![ArgCmp::eq(6, 0)]).check(),
        Err(Error::InvalidArg(6)),
    ));
    assert!(rule(Action::Errno(1), vec![ArgCmp::eq(1, 0), ArgCmp::ne(1, 1)])
        .check()
        .is_ok());
}

#[test]
fn skip_rule_is_allowed() {
    let mut filter = Filter::new_native(Action::Allow).unwrap();
    assert!(filter.add_rule(Action::Errno(1), Syscall::Skip, vec![ArgCmp::eq(5, 0)]).is_ok());
}
