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
    /// A skip rule requires the skip-syscall option to be enabled.
    SkipNotEnabled,
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
    pub fn eq(arg: u32, val: u64) -> (res: Self)
        ensures res == (ArgCmp { arg, op: Compare::Eq, datum_a: val, datum_b: 0 })
    {
        ArgCmp { arg, op: Compare::Eq, datum_a: val, datum_b: 0 }
    }

    /// Tests whether the argument at index `arg` does not equal `val`.
    pub fn ne(arg: u32, val: u64) -> (res: Self)
        ensures res == (ArgCmp { arg, op: Compare::Ne, datum_a: val, datum_b: 0 })
    {
        ArgCmp { arg, op: Compare::Ne, datum_a: val, datum_b: 0 }
    }

    /// Tests whether the argument at index `arg` is less than `val`.
    pub fn lt(arg: u32, val: u64) -> (res: Self)
        ensures res == (ArgCmp { arg, op: Compare::Lt, datum_a: val, datum_b: 0 })
    {
        ArgCmp { arg, op: Compare::Lt, datum_a: val, datum_b: 0 }
    }

    /// Tests whether the argument at index `arg` is less than or equal to `val`.
    pub fn le(arg: u32, val: u64) -> (res: Self)
        ensures res == (ArgCmp { arg, op: Compare::Le, datum_a: val, datum_b: 0 })
    {
        ArgCmp { arg, op: Compare::Le, datum_a: val, datum_b: 0 }
    }

    /// Tests whether the argument at index `arg` is greater than `val`.
    pub fn gt(arg: u32, val: u64) -> (res: Self)
        ensures res == (ArgCmp { arg, op: Compare::Gt, datum_a: val, datum_b: 0 })
    {
        ArgCmp { arg, op: Compare::Gt, datum_a: val, datum_b: 0 }
    }

    /// Tests whether the argument at index `arg` is greater than or equal to `val`.
    pub fn ge(arg: u32, val: u64) -> (res: Self)
        ensures res == (ArgCmp { arg, op: Compare::Ge, datum_a: val, datum_b: 0 })
    {
        ArgCmp { arg, op: Compare::Ge, datum_a: val, datum_b: 0 }
    }

    /// Tests whether the argument at index `arg` equals `val` under `mask`.
    pub fn masked_eq(arg: u32, mask: u64, val: u64) -> (res: Self)
        ensures res == (ArgCmp { arg, op: Compare::MaskedEq, datum_a: mask, datum_b: val })
    {
        ArgCmp { arg, op: Compare::MaskedEq, datum_a: mask, datum_b: val }
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
    /// Checks whether this rule is valid for the given filter attributes.
    pub fn check(&self, _attrs: &Attrs) -> (res: Result<(), Error>)
        ensures (res is Ok) == self.wf(*_attrs)
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

    /// Creates a filter with default action `act_default` and no architectures enabled.
    pub fn new(act_default: Action) -> (res: Result<Filter, Error>)
        ensures res matches Ok(f) ==> {
            &&& f.wf()
            &&& f.policy().attrs.act_default == act_default
            &&& f.policy().archs@.len() == 0
        }
    {
        act_default.check()?;
        Ok(Filter {
            policy: Policy {
                attrs: Attrs { act_default, act_badarch: Action::KillThread, ..Attrs::default() },
                archs: Vec::new(),
                rules: Vec::new(),
            },
        })
    }

    /// Creates a filter over the running architecture with default action `act_default`.
    pub fn new_native(act_default: Action) -> (res: Result<Filter, Error>)
        ensures res matches Ok(f) ==> {
            &&& f.wf()
            &&& f.policy().attrs.act_default == act_default
            &&& f.policy().archs@.len() == 1
        }
    {
        let mut filter = Self::new(act_default)?;
        filter.add_arch(Arch::native()?)?;
        Ok(filter)
    }

    /// Adds `arch` to the architectures covered by this filter's rules.
    pub fn add_arch(&mut self, arch: Arch) -> (res: Result<(), Error>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            final(self).policy().attrs == old(self).policy().attrs,
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
            res is Ok ==> final(self).policy().rules@ == old(self).policy().rules@.push(
                Rule { action, syscall, conds, exact: false }),
    {
        let rule = Rule { action, syscall, conds, exact: false };
        rule.check(&self.policy.attrs)?;

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

    /// Sets the action for syscalls from architectures this filter does not cover.
    pub fn on_badarch(&mut self, act_badarch: Action) -> (res: Result<(), Error>)
        requires old(self).wf()
        ensures
            final(self).wf(),
            res is Ok ==> final(self).policy().attrs.act_badarch == act_badarch,
    {
        act_badarch.check()?;
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

    /// Compiles this filter into a classic BPF program.
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

    /// Compiles this filter and installs it on the calling thread.
    #[cfg(target_os = "linux")]
    pub fn install(&self) -> Result<(), Error>
        requires self.wf()
    {
        match self.to_cbpf() {
            Ok(prog) => prog.install(&self.policy.attrs),
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
impl Attrs {
    /// The `SECCOMP_FILTER_FLAG_*` bits in `linux/seccomp.h`.
    const FLAG_TSYNC: u64 = 1 << 0;
    const FLAG_LOG: u64 = 1 << 1;
    const FLAG_SPEC_ALLOW: u64 = 1 << 2;

    /// The flag word these attributes ask `seccomp(2)` for.
    fn filter_flags(&self) -> u64 {
        let mut flags: u64 = 0;
        if self.ctl_tsync {
            flags = flags | Self::FLAG_TSYNC;
        }
        if self.ctl_log {
            flags = flags | Self::FLAG_LOG;
        }
        if self.ctl_ssb {
            flags = flags | Self::FLAG_SPEC_ALLOW;
        }
        flags
    }
}

#[cfg(target_os = "linux")]
impl Program {
    /// Loads this program into the calling thread as its seccomp filter.
    #[verifier::external_body]
    pub fn install(&self, attrs: &Attrs) -> Result<(), Error> {
        // `seccomp()` answers EACCES to a thread that holds neither CAP_SYS_ADMIN nor
        // `no_new_privs`, so `ctl_nnp` goes in first.
        if attrs.ctl_nnp {
            let rc = unsafe { libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) };
            if rc != 0 {
                return Err(Error::NoNewPrivs(Error::errno()));
            }
        }

        let mut filter: Vec<_> = self.assemble();

        // The kernel copies the program out of `sock_fprog` before it returns, so the
        // buffer only has to outlive the call.
        let fprog = libc::sock_fprog {
            len: filter.len() as u16,
            filter: filter.as_mut_ptr() as *mut libc::sock_filter,
        };
        let rc = unsafe {
            libc::syscall(
                libc::SYS_seccomp,
                libc::SECCOMP_SET_MODE_FILTER as libc::c_ulong,
                attrs.filter_flags() as libc::c_ulong,
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
