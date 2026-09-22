//! Top-level APIs for building and installing policies.

use vstd::prelude::*;
use crate::spec::{policy::*, cbpf::*};
use crate::compiler::CompileError;

verus! {

/// An error while creating, updating, compiling, or installing a filter.
#[derive(Debug)]
pub enum Error {
    /// An action contains an invalid value.
    BadAction,
    /// A rule has the same action as the filter's default.
    ActionIsDefault,
    /// A condition uses an argument index outside zero through five.
    ArgumentOutOfRange(u32),
    /// The filter already includes this architecture.
    DuplicateArch,
    /// The native architecture is not supported.
    UnsupportedArch,
    /// The policy could not be compiled into a filter program.
    Compile(CompileError),
    /// Setting `no_new_privs` failed with this errno.
    NoNewPrivs(i32),
    /// Installing the seccomp filter failed with this errno.
    SetModeFilter(i32),
}

impl Arch {
    /// Returns the architecture this binary runs on, or an error if it is unsupported.
    pub fn native() -> Result<Arch, Error> {
        if cfg!(all(target_arch = "x86_64", target_pointer_width = "32")) {
            Ok(Arch::X32)
        } else if cfg!(target_arch = "x86_64") {
            Ok(Arch::X86_64)
        } else if cfg!(target_arch = "aarch64") {
            Ok(Arch::Aarch64)
        } else if cfg!(target_arch = "x86") {
            Ok(Arch::X86)
        } else if cfg!(target_arch = "arm") {
            Ok(Arch::Arm)
        } else {
            Err(Error::UnsupportedArch)
        }
    }
}

impl ArgCmp {
    /// Tests whether the argument at index `arg` equals `val`.
    pub fn eq(arg: u32, val: u64) -> Self {
        ArgCmp { arg, op: Compare::Eq, a: val, b: 0 }
    }

    /// Tests whether the argument at index `arg` does not equal `val`.
    pub fn ne(arg: u32, val: u64) -> Self {
        ArgCmp { arg, op: Compare::Ne, a: val, b: 0 }
    }

    /// Tests whether the argument at index `arg` is less than `val`.
    pub fn lt(arg: u32, val: u64) -> Self {
        ArgCmp { arg, op: Compare::Lt, a: val, b: 0 }
    }

    /// Tests whether the argument at index `arg` is less than or equal to `val`.
    pub fn le(arg: u32, val: u64) -> Self {
        ArgCmp { arg, op: Compare::Le, a: val, b: 0 }
    }

    /// Tests whether the argument at index `arg` is greater than `val`.
    pub fn gt(arg: u32, val: u64) -> Self {
        ArgCmp { arg, op: Compare::Gt, a: val, b: 0 }
    }

    /// Tests whether the argument at index `arg` is greater than or equal to `val`.
    pub fn ge(arg: u32, val: u64) -> Self {
        ArgCmp { arg, op: Compare::Ge, a: val, b: 0 }
    }

    /// Tests whether the argument at index `arg` equals `val` under `mask`.
    pub fn masked_eq(arg: u32, mask: u64, val: u64) -> Self {
        ArgCmp { arg, op: Compare::MaskedEq, a: mask, b: val }
    }
}

impl Action {
    /// Checks whether this action contains a valid value.
    pub fn check(&self) -> (res: Result<(), Error>)
        ensures
            (res is Ok) == self.wf(),
            res matches Err(err) ==> err is BadAction,
    {
        match self {
            Action::Errno(e) if (*e as u32) >= Self::MAX_ERRNO => Err(Error::BadAction),
            _ => Ok(()),
        }
    }
}

impl Rule {
    /// Checks whether this rule has a valid action and argument indices.
    pub fn check(&self) -> (res: Result<(), Error>)
        ensures (res is Ok) == self.wf()
    {
        self.action.check()?;
        let mut i: usize = 0;
        while i < self.conds.len()
            invariant
                self.action.wf(),
                i <= self.conds@.len(),
                forall |k: int| #![trigger self.conds@[k]]
                    0 <= k < i ==> self.conds@[k].arg < Self::ARG_COUNT_MAX,
            decreases self.conds@.len() - i
        {
            if self.conds[i].arg >= Self::ARG_COUNT_MAX {
                return Err(Error::ArgumentOutOfRange(self.conds[i].arg));
            }
            i += 1;
        }
        Ok(())
    }
}

/// A policy under construction and its filter options.
pub struct Filter {
    pub policy: Policy,
    /// Set `no_new_privs` before installing the filter.
    pub ctl_nnp: bool,
    /// Synchronize the installed filter across all threads.
    pub ctl_tsync: bool,
    /// Request logging of all filter actions except `Allow`.
    pub ctl_log: bool,
    // TODO: notification related flags.
    // pub api_sysrawrc: bool,
    // pub ctl_waitkill: bool,
}

impl Filter {
    /// Whether the collected policy is well-formed.
    pub open spec fn wf(self) -> bool {
        self.policy.wf()
    }

    /// Creates a filter with default action `act_no_match` and no architectures enabled.
    pub fn new(act_no_match: Action) -> (res: Result<Filter, Error>)
        ensures res matches Ok(f) ==> {
            &&& f.wf()
            &&& f.policy.act_no_match == act_no_match
            &&& f.policy.act_bad_arch == Action::KillThread
            &&& f.policy.archs@.len() == 0
            &&& f.policy.rules@.len() == 0
        }
    {
        act_no_match.check()?;
        Ok(Filter {
            policy: Policy {
                archs: Vec::new(),
                rules: Vec::new(),
                act_no_match,
                act_bad_arch: Action::KillThread,
            },
            ctl_nnp: true,
            ctl_tsync: false,
            ctl_log: false,
        })
    }

    /// Creates a filter over the running architecture with default action `act_no_match`.
    pub fn new_native(act_no_match: Action) -> (res: Result<Filter, Error>)
        ensures res matches Ok(f) ==> {
            &&& f.wf()
            &&& f.policy.act_no_match == act_no_match
            &&& f.policy.act_bad_arch == Action::KillThread
            &&& f.policy.archs@.len() == 1
            &&& f.policy.rules@.len() == 0
        }
    {
        let mut filter = Self::new(act_no_match)?;
        filter.add_arch(Arch::native()?)?;
        Ok(filter)
    }

    /// Adds `arch` to the architectures covered by this filter's rules.
    pub fn add_arch(&mut self, arch: Arch) -> (res: Result<(), Error>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            final(self).policy.act_no_match == old(self).policy.act_no_match,
            final(self).policy.act_bad_arch == old(self).policy.act_bad_arch,
            final(self).policy.rules == old(self).policy.rules,
            res is Ok ==> final(self).policy.archs@ == old(self).policy.archs@.push(arch),
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
                return Err(Error::DuplicateArch);
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

    /// Applies `action` to `syscall` when every argument test in `conds` holds.
    pub fn add_rule(&mut self, action: Action, syscall: Syscall, conds: Vec<ArgCmp>)
        -> (res: Result<(), Error>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            res is Ok ==> final(self).policy.rules@ == old(self).policy.rules@.push(
                Rule { action, syscall, conds, exact: false }),
    {
        let rule = Rule { action, syscall, conds, exact: false };
        rule.check()?;
        if rule.action.to_ret() == self.policy.act_no_match.to_ret() {
            return Err(Error::ActionIsDefault);
        }

        let ghost prev = self.policy.rules@;
        self.policy.rules.push(rule);
        proof {
            assert forall |k: int| 0 <= k < self.policy.rules@.len()
                implies #[trigger] self.policy.rules@[k].wf() by {
                if k < prev.len() {
                    assert(prev[k].wf());
                }
            }
        }
        Ok(())
    }

    /// Sets the action for syscalls from architectures this filter does not cover.
    pub fn on_bad_arch(&mut self, act: Action) -> (res: Result<(), Error>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            res is Ok ==> final(self).policy.act_bad_arch == act,
    {
        act.check()?;
        self.policy.act_bad_arch = act;
        Ok(())
    }

    /// Skips setting `no_new_privs` during filter installation.
    pub fn allow_new_privileges(&mut self)
        ensures final(self).policy == old(self).policy
    {
        self.ctl_nnp = false;
    }

    /// When installing, set all threads in this process to use the same seccomp filter chain.
    pub fn enable_thread_sync(&mut self)
        ensures final(self).policy == old(self).policy
    {
        self.ctl_tsync = true;
    }

    /// Requests kernel audit records for non-allow actions when installing the filter
    /// (requires `auditd` and [ausearch(8)](https://man7.org/linux/man-pages/man8/ausearch.8.html) to view logs).
    pub fn request_audit_logging(&mut self)
        ensures final(self).policy == old(self).policy
    {
        self.ctl_log = true;
    }

    /// Compiles this filter into a classic BPF program.
    pub fn to_cbpf(&self) -> (res: Result<Program, CompileError>)
        requires self.wf()
        ensures res matches Ok(prog) ==>
            // Compiled program is well-formed.
            prog.wf() &&
            // Compiled program runs error-free and produces an action accepted by the policy.
            forall |data: &[u8]| #[trigger] Event::parse(data) matches Some(ev) ==> {
                &&& prog.eval(data) matches Outcome::Return(ret)
                &&& self.policy.eval(ev, Action::from_ret(ret))
            }
    {
        self.policy.to_cbpf()
    }

    /// Compiles this filter and installs it on the calling thread.
    #[cfg(target_os = "linux")]
    pub fn install(&self) -> Result<(), Error>
        requires self.wf()
    {
        match self.to_cbpf() {
            Ok(prog) => prog.install(self),
            Err(err) => Err(Error::Compile(err)),
        }
    }
}

#[cfg(target_os = "linux")]
impl Error {
    /// The errno the last failing libc call left behind.
    #[verifier::external_body]
    fn errno() -> i32 {
        std::io::Error::last_os_error().raw_os_error().unwrap_or(0)
    }
}

#[cfg(target_os = "linux")]
impl Filter {
    /// The `SECCOMP_FILTER_FLAG_*` bits in `linux/seccomp.h`.
    const FLAG_TSYNC: u64 = 1 << 0;
    const FLAG_LOG: u64 = 1 << 1;

    /// Generates a flag for `seccomp(2)`
    fn filter_flags(&self) -> u64 {
        let mut flags: u64 = 0;
        if self.ctl_tsync {
            flags = flags | Self::FLAG_TSYNC;
        }
        if self.ctl_log {
            flags = flags | Self::FLAG_LOG;
        }
        flags
    }
}

#[cfg(target_os = "linux")]
impl Program {
    /// Loads this program using the filter's installation options.
    #[verifier::external_body]
    pub fn install(&self, filter: &Filter) -> Result<(), Error> {
        // `seccomp()` answers EACCES to a thread that holds neither CAP_SYS_ADMIN nor
        // `no_new_privs`, so `ctl_nnp` goes in first.
        if filter.ctl_nnp {
            let rc = unsafe { libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) };
            if rc != 0 {
                return Err(Error::NoNewPrivs(Error::errno()));
            }
        }

        let mut instrs: Vec<_> = self.assemble();

        // The kernel copies the program out of `sock_fprog` before it returns, so the
        // buffer only has to outlive the call.
        let fprog = libc::sock_fprog {
            len: instrs.len() as u16,
            filter: instrs.as_mut_ptr() as *mut libc::sock_filter,
        };
        let rc = unsafe {
            libc::syscall(
                libc::SYS_seccomp,
                libc::SECCOMP_SET_MODE_FILTER as libc::c_ulong,
                filter.filter_flags() as libc::c_ulong,
                &fprog as *const libc::sock_fprog,
            )
        };
        if rc != 0 {
            // A thread that refuses TSYNC comes back as its own id rather than as -1,
            // unless `SECCOMP_FILTER_FLAG_TSYNC_ESRCH` is set, which this module leaves off.
            let errno = if rc < 0 { Error::errno() } else { libc::ESRCH };
            return Err(Error::SetModeFilter(errno));
        }
        Ok(())
    }
}

} // verus!
