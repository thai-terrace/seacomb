//! Top-level APIs for building and installing policies.

use vstd::prelude::*;
use crate::spec::{policy::*, cbpf::*};
use crate::compiler::CompileError;

verus! {

/// Why a filter turned an update down, named after the errno libseccomp answers.
#[derive(Debug)]
pub enum FilterError {
    /// An action the kernel leaves no room for, `-EINVAL`.
    BadAction,
    /// A rule whose action only repeats the filter's default, `-EACCES`.
    ActionIsDefault,
    /// Argument tests that do not name distinct arguments of the syscall, `-EINVAL`.
    BadConditions,
    /// An architecture the filter already covers, `-EEXIST`.
    DuplicateArch,
}

impl Arch {
    /// The architecture this binary runs on, when the policy language has a token for it.
    pub fn native() -> Option<Arch> {
        if cfg!(all(target_arch = "x86_64", target_pointer_width = "32")) {
            Some(Arch::X32)
        } else if cfg!(target_arch = "x86_64") {
            Some(Arch::X86_64)
        } else if cfg!(target_arch = "aarch64") {
            Some(Arch::Aarch64)
        } else if cfg!(target_arch = "x86") {
            Some(Arch::X86)
        } else if cfg!(target_arch = "arm") {
            Some(Arch::Arm)
        } else {
            None
        }
    }
}

impl Action {
    /// Executable version of [`Action::wf`].
    pub fn check(&self) -> (res: bool)
        ensures res == self.wf()
    {
        match self {
            Action::Errno(e) => (*e as u32) < Self::MAX_ERRNO,
            _ => true,
        }
    }
}

impl Rule {
    /// Executable version of [`Rule::conds_wf`].
    pub fn check_conds(&self) -> (res: bool)
        ensures res == self.conds_wf()
    {
        if self.conds.len() > Self::ARG_COUNT_MAX as usize {
            return false;
        }
        let mut i: usize = 0;
        while i < self.conds.len()
            invariant
                i <= self.conds@.len() <= Self::ARG_COUNT_MAX,
                forall |k: int| #![trigger self.conds@[k]]
                    0 <= k < i ==> self.conds@[k].arg < Self::ARG_COUNT_MAX,
                forall |k: int, l: int| #![trigger self.conds@[k], self.conds@[l]]
                    0 <= k < l < i ==> self.conds@[k].arg != self.conds@[l].arg,
            decreases self.conds@.len() - i
        {
            if self.conds[i].arg >= Self::ARG_COUNT_MAX {
                return false;
            }
            let mut j: usize = 0;
            while j < i
                invariant
                    j <= i < self.conds@.len(),
                    forall |k: int| #![trigger self.conds@[k]]
                        0 <= k < j ==> self.conds@[k].arg != self.conds@[i as int].arg,
                decreases i - j
            {
                if self.conds[j].arg == self.conds[i].arg {
                    return false;
                }
                j += 1;
            }
            i += 1;
        }
        true
    }
}

/// A policy under construction, which only its own methods can extend.
pub struct Filter {
    policy: Policy,
}

impl Filter {
    /// The policy this filter has collected.
    pub closed spec fn policy(self) -> Policy {
        self.policy
    }

    /// Whether the collected policy is well-formed.
    pub open spec fn wf(self) -> bool {
        self.policy().wf()
    }

    /// `seccomp_init`: a filter over no architecture that answers `act_default` to everything.
    pub fn new(act_default: Action) -> (res: Result<Filter, FilterError>)
        ensures res matches Ok(f) ==> f.wf() && f.policy().attrs.act_default == act_default
    {
        if !act_default.check() {
            return Err(FilterError::BadAction);
        }
        Ok(Filter {
            policy: Policy {
                attrs: Attrs { act_default, act_badarch: Action::KillThread, ..Attrs::default() },
                archs: Vec::new(),
                priorities: Vec::new(),
                rules: Vec::new(),
            },
        })
    }

    /// `seccomp_arch_add`: brings `arch` into the policy's scope.
    pub fn add_arch(&mut self, arch: Arch) -> (res: Result<(), FilterError>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            res is Ok ==> final(self).policy().archs@ == old(self).policy().archs@.push(arch),
    {
        let mut i: usize = 0;
        while i < self.policy.archs.len()
            invariant
                self.wf(),
                i <= self.policy.archs@.len(),
                forall |k: int| #![trigger self.policy.archs@[k]]
                    0 <= k < i ==> self.policy.archs@[k] != arch,
            decreases self.policy.archs@.len() - i
        {
            if self.policy.archs[i] == arch {
                return Err(FilterError::DuplicateArch);
            }
            i += 1;
        }

        let ghost prev = self.policy.archs@;
        self.policy.archs.push(arch);
        proof {
            assert forall |k: int, l: int| 0 <= k < l < self.policy.archs@.len()
                implies #[trigger] self.policy.archs@[k] != #[trigger] self.policy.archs@[l] by {
                if l < prev.len() {
                    assert(prev[k] != prev[l]);
                } else {
                    assert(prev[k] != arch);
                }
            }
        }
        Ok(())
    }

    /// `seccomp_rule_add`: answers `action` to `syscall` when every test in `conds` holds.
    pub fn add_rule(&mut self, action: Action, syscall: SyscallName, conds: Vec<ArgCmp>)
        -> (res: Result<(), FilterError>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            res is Ok ==> final(self).policy().rules@ == old(self).policy().rules@.push(
                Rule { action, syscall: Syscall::Name(syscall), conds, exact: false }),
    {
        let rule = Rule { action, syscall: Syscall::Name(syscall), conds, exact: false };
        if !rule.action.check() {
            return Err(FilterError::BadAction);
        }
        // `Action::to_ret` is injective, by `Action::lemma_to_ret`, so it settles the comparison.
        if rule.action.to_ret() == self.policy.attrs.act_default.to_ret() {
            return Err(FilterError::ActionIsDefault);
        }
        if !rule.check_conds() {
            return Err(FilterError::BadConditions);
        }

        let ghost prev = self.policy.rules@;
        let ghost attrs = self.policy.attrs;
        self.policy.rules.push(rule);
        proof {
            assert forall |k: int| 0 <= k < self.policy.rules@.len()
                implies #[trigger] self.policy.rules@[k].wf(attrs) by {
                if k < prev.len() {
                    assert(prev[k].wf(attrs));
                }
            }
        }
        Ok(())
    }

    /// `seccomp_attr_set` of `SCMP_FLTATR_ACT_BADARCH`: what an event from another
    /// architecture is answered with.
    pub fn on_bad_arch(&mut self, act_badarch: Action) -> (res: Result<(), FilterError>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            res is Ok ==> final(self).policy().attrs.act_badarch == act_badarch,
    {
        if !act_badarch.check() {
            return Err(FilterError::BadAction);
        }
        let ghost attrs = self.policy.attrs;
        self.policy.attrs.act_badarch = act_badarch;
        proof {
            assert forall |k: int| 0 <= k < self.policy.rules@.len()
                implies #[trigger] self.policy.rules@[k].wf(self.policy.attrs) by {
                assert(self.policy.rules@[k].wf(attrs));
            }
        }
        Ok(())
    }

    /// The filter program this policy compiles to, which `seccomp_export_bpf` writes out.
    pub fn to_cbpf(&self) -> (res: Result<Program, CompileError>)
        requires self.wf()
        ensures res matches Ok(prog) ==>
            // Compiled program is well-formed.
            prog.wf() &&
            // Compiled program runs error-free and produces an action accepted by the policy.
            forall |data: &[u8]| #[trigger] Event::parse(data) matches Some(ev) ==> {
                &&& prog.eval(data) matches Outcome::Return(ret)
                &&& self.policy().eval(ev, Action::from_ret(ret))
            }
    {
        self.policy.to_cbpf()
    }

    /// `seccomp_load`: compiles the policy and loads it into the calling thread.
    #[cfg(target_os = "linux")]
    pub fn install(&self) -> Result<(), crate::seccomp::InstallError>
        requires self.wf()
    {
        self.policy.install()
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    impl Filter {
        /// A filter over the running architecture that lets through whatever no rule claims.
        fn allow_native() -> Filter {
            let mut filter = Filter::new(Action::Allow).ok().unwrap();
            filter.add_arch(Arch::native().unwrap()).ok().unwrap();
            filter
        }
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
        let mut filter = Filter::allow_native();
        assert!(filter.add_arch(Arch::native().unwrap()).is_err());
    }

    /// A rule that only repeats the default action is turned down.
    #[test]
    fn rule_repeats_default() {
        let mut filter = Filter::allow_native();
        assert!(filter.add_rule(Action::Allow, SyscallName::Getpid, vec![]).is_err());
    }

    /// Two tests of one argument in a single rule are turned down.
    #[test]
    fn duplicate_argument() {
        let mut filter = Filter::allow_native();
        let conds = vec![
            ArgCmp { arg: 1, op: Compare::Eq, datum_a: 0, datum_b: 0 },
            ArgCmp { arg: 1, op: Compare::Ne, datum_a: 1, datum_b: 0 },
        ];
        assert!(filter.add_rule(Action::Errno(1), SyscallName::Lseek, conds).is_err());
    }

    /// An argument the architecture does not have is turned down.
    #[test]
    fn argument_out_of_range() {
        let mut filter = Filter::allow_native();
        let conds = vec![ArgCmp { arg: 6, op: Compare::Eq, datum_a: 0, datum_b: 0 }];
        assert!(filter.add_rule(Action::Errno(1), SyscallName::Lseek, conds).is_err());
    }

    /// Tests that install the filter and watch what the kernel makes of it.
    #[cfg(target_os = "linux")]
    mod install {
        use super::*;

        /// How a child process that ran under a filter ended.
        #[derive(Debug, PartialEq, Eq)]
        enum Child {
            /// Left through `_exit` with this status.
            Exited(i32),
            /// Killed by this signal.
            Killed(i32),
        }

        impl Child {
            /// The status the child leaves with when the filter never reaches the kernel.
            const INSTALL_FAILED: i32 = 70;

            /// The errno the last failing libc call left behind.
            fn errno() -> i32 {
                std::io::Error::last_os_error().raw_os_error().unwrap_or(0)
            }

            /// Runs `body` in a child process that has `filter` installed.
            fn run(filter: &Filter, body: impl FnOnce() -> i32) -> Child {
                unsafe {
                    let pid = libc::fork();
                    assert!(pid >= 0, "fork failed");
                    if pid == 0 {
                        // A denied exit would leave the child spinning, so cap how long it lives.
                        libc::alarm(10);
                        let status = match filter.install() {
                            Ok(()) => body(),
                            Err(_) => Self::INSTALL_FAILED,
                        };
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
        }

        /// A filter with no rules and an `SCMP_ACT_ALLOW` default lets the child run on.
        #[test]
        fn allow_all() {
            let filter = Filter::allow_native();
            let child = Child::run(&filter, || unsafe {
                if libc::syscall(libc::SYS_getpid) > 0 { 0 } else { 1 }
            });
            assert_eq!(child, Child::Exited(0));
        }

        /// An `SCMP_ACT_ERRNO` rule fails its own syscall and no other.
        #[test]
        fn errno_on_getpid() {
            let mut filter = Filter::allow_native();
            filter.add_rule(Action::Errno(libc::EPERM as u16), SyscallName::Getpid, vec![]).unwrap();
            let child = Child::run(&filter, || unsafe {
                if libc::syscall(libc::SYS_getpid) != -1 { return 1; }
                if Child::errno() != libc::EPERM { return 2; }
                if libc::syscall(libc::SYS_getppid) <= 0 { return 3; }
                0
            });
            assert_eq!(child, Child::Exited(0));
        }

        /// An argument test narrows a rule to the calls that pass it.
        #[test]
        fn errno_on_first_argument() {
            let mut filter = Filter::allow_native();
            let conds = vec![ArgCmp { arg: 0, op: Compare::Eq, datum_a: 42, datum_b: 0 }];
            filter.add_rule(Action::Errno(libc::EPERM as u16), SyscallName::Lseek, conds).unwrap();
            let child = Child::run(&filter, || {
                // `lseek` on a descriptor nothing opened, which the kernel refuses with EBADF.
                let lseek = |fd: libc::c_long, offset: libc::c_long| unsafe {
                    libc::syscall(libc::SYS_lseek, fd, offset, libc::SEEK_SET as libc::c_long)
                };
                if lseek(42, 0) != -1 { return 1; }
                if Child::errno() != libc::EPERM { return 2; }
                if lseek(43, 0) != -1 { return 3; }
                if Child::errno() != libc::EBADF { return 4; }
                0
            });
            assert_eq!(child, Child::Exited(0));
        }

        /// An `SCMP_ACT_KILL_PROCESS` rule takes the child down with SIGSYS.
        #[test]
        fn kill_process_on_getppid() {
            let mut filter = Filter::allow_native();
            filter.add_rule(Action::KillProcess, SyscallName::Getppid, vec![]).unwrap();
            let child = Child::run(&filter, || unsafe {
                libc::syscall(libc::SYS_getppid);
                0
            });
            assert_eq!(child, Child::Killed(libc::SIGSYS));
        }

        /// An argument test on a 64-bit architecture looks at both words of the argument.
        #[cfg(target_pointer_width = "64")]
        #[test]
        fn errno_on_high_word_of_argument() {
            let mut filter = Filter::allow_native();
            let conds = vec![ArgCmp { arg: 1, op: Compare::Eq, datum_a: 0x1_0000_0000, datum_b: 0 }];
            filter.add_rule(Action::Errno(libc::EPERM as u16), SyscallName::Lseek, conds).unwrap();
            let child = Child::run(&filter, || {
                // `lseek` on a descriptor nothing opened, which the kernel refuses with EBADF.
                let lseek = |fd: libc::c_long, offset: libc::c_long| unsafe {
                    libc::syscall(libc::SYS_lseek, fd, offset, libc::SEEK_SET as libc::c_long)
                };
                if lseek(43, 0x1_0000_0000) != -1 { return 1; }
                if Child::errno() != libc::EPERM { return 2; }
                if lseek(43, 1) != -1 { return 3; }
                if Child::errno() != libc::EBADF { return 4; }
                0
            });
            assert_eq!(child, Child::Exited(0));
        }

        /// An event from an architecture the filter leaves out takes `act_badarch`.
        #[test]
        fn badarch_kills() {
            let absent = if Arch::native().unwrap() == Arch::X86 { Arch::Aarch64 } else { Arch::X86 };
            let mut filter = Filter::new(Action::Allow).ok().unwrap();
            filter.add_arch(absent).ok().unwrap();
            filter.on_bad_arch(Action::KillProcess).ok().unwrap();
            let child = Child::run(&filter, || unsafe {
                libc::syscall(libc::SYS_getpid);
                0
            });
            assert_eq!(child, Child::Killed(libc::SIGSYS));
        }
    }
}
