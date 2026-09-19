//! Abstract syntax and semantics of the libseccomp policy/rule language.

use vstd::prelude::*;
pub use super::syscall::*;

verus! {

/// Architecture tokens `SCMP_ARCH_*` (excluding `SCMP_ARCH_NATIVE`).
pub enum Arch { X86, X86_64, X32, Arm, Aarch64 }

/// Filter actions (`SCMP_ACT_*`).
pub enum Action {
    KillProcess,
    KillThread,
    Trap(u16),
    Errno(u16),
    Trace(u16),
    Log,
    Allow,
    Notify,
}

/// Comparison operators `scmp_compare`.
pub enum Compare { Ne, Lt, Le, Eq, Ge, Gt, MaskedEq }

/// One argument test `scmp_arg_cmp`.
pub struct ArgCmp {
    pub arg: u32,
    pub op: Compare,
    pub datum_a: u64,
    /// For MaskedEq only: `datum_a` is the mask, `datum_b` the value.
    pub datum_b: u64,
}

/// The `int syscall` parameter as written by the policy author.
pub enum Syscall {
    Name(SyscallName),
    /// Only allowed with `api_tskip`.
    Skip,
}

/// One `seccomp_rule_add[_exact][_array]` call.
pub struct Rule {
    pub action: Action,
    pub syscall: Syscall,
    pub conds: Seq<ArgCmp>,
    /// `true` for the `_exact` variants (fail instead of adapting the rule per arch).
    pub exact: bool,
}

/// One `seccomp_syscall_priority` call.
pub struct Priority {
    pub syscall: Syscall,
    pub priority: u8,
}

/// `SCMP_FLTATR_CTL_OPTIMIZE` values.
pub enum Optimize { ByPriority, BinaryTree }

/// Filter attributes, `enum scmp_filter_attr` (`struct db_filter_attr`).
pub struct Attrs {
    pub act_default: Action,
    pub act_badarch: Action,
    pub ctl_nnp: bool,
    pub ctl_tsync: bool,
    pub api_tskip: bool,
    pub ctl_log: bool,
    pub ctl_ssb: bool,
    pub ctl_optimize: Optimize,
    pub api_sysrawrc: bool,
    pub ctl_waitkill: bool,
}

/// A whole filter context (`scmp_filter_ctx`), viewed declaratively.
pub struct Policy {
    pub attrs: Attrs,
    pub archs: Seq<Arch>,
    pub priorities: Seq<Priority>,
    pub rules: Seq<Rule>,
}

impl Default for Optimize {
    fn default() -> Self { Optimize::ByPriority }
}

impl Default for Attrs {
    fn default() -> Self {
        Attrs {
            // seccomp_init's argument
            act_default: Action::KillThread,
            act_badarch: Action::KillThread,
            ctl_nnp: true,
            ctl_tsync: false,
            api_tskip: false,
            ctl_log: false,
            ctl_ssb: false,
            ctl_optimize: Optimize::default(),
            api_sysrawrc: false,
            ctl_waitkill: false,
        }
    }
}

impl Action {
    /// `src/system.h`: largest errno accepted by SCMP_ACT_ERRNO
    pub const MAX_ERRNO: u32 = 4095;

    /// `sys_chk_seccomp_action` (kernel-support probing aside).
    pub open spec fn wf(self) -> bool {
        match self {
            Action::Errno(e) => (e as u32) < Self::MAX_ERRNO,
            _ => true,
        }
    }
}

impl Syscall {
    /// `_syscall_valid` in `src/api.c`: the reserved range is rejected; `Event::SKIP_NR` needs `api_tskip`.
    pub open spec fn wf(self, api_tskip: bool) -> bool {
        match self {
            Syscall::Name(_) => true,
            Syscall::Skip => api_tskip,
        }
    }
}

impl Rule {
    /// `src/arch.h`.
    pub const ARG_COUNT_MAX: u32 = 6;

    /// `db_col_rule_add`.
    pub open spec fn conds_wf(self) -> bool {
        &&& self.conds.len() <= Self::ARG_COUNT_MAX as nat
        &&& forall |i: int| #![trigger self.conds[i]]
                0 <= i < self.conds.len() ==> self.conds[i].arg < Self::ARG_COUNT_MAX
        &&& forall |i: int, j: int| #![trigger self.conds[i], self.conds[j]]
                0 <= i < j < self.conds.len() ==> self.conds[i].arg != self.conds[j].arg
    }

    /// `seccomp_rule_add*`.
    pub open spec fn wf(self, attrs: Attrs) -> bool {
        &&& self.action.wf()
        &&& self.action != attrs.act_default
        &&& self.syscall.wf(attrs.api_tskip)
        &&& self.conds_wf()
    }
}

impl Policy {
    /// `db_col_db_add`: no duplicate arch (-EEXIST).
    pub open spec fn archs_wf(self) -> bool {
        forall |i: int, j: int| #![trigger self.archs[i], self.archs[j]]
            0 <= i < j < self.archs.len() ==> self.archs[i] != self.archs[j]
    }

    pub open spec fn wf(self) -> bool {
        &&& self.attrs.act_default.wf()
        &&& self.attrs.act_badarch.wf()
        &&& self.archs_wf()
        &&& forall |i: int| #![trigger self.rules[i]]
                0 <= i < self.rules.len() ==> self.rules[i].wf(self.attrs)
        &&& forall |i: int| #![trigger self.priorities[i]]
                0 <= i < self.priorities.len()
                    ==> self.priorities[i].syscall.wf(self.attrs.api_tskip)
    }
}

} // verus!

// Semantics
verus! {

/// `seccomp_data` without the instruction pointer.
pub struct Event {
    pub arch: u32,
    pub nr: i32,
    pub args: Seq<u64>,
}

/// Results of matching a syscall name against an event.
pub enum SyscallMatch {
    Exact,
    /// Matches a `socketcall` or `ipc` call.
    Mux,
    None,
}

impl Event {
    pub const SKIP_NR: i32 = -1;

    pub open spec fn is_skip(self) -> bool { self.nr == Self::SKIP_NR }

    /// `nr >= X32_SYSCALL_BIT` (`src/arch-x32.h`) as the BPF's unsigned comparison sees it.
    pub open spec fn x32_bit(self) -> bool { self.nr < 0 || self.nr >= 0x4000_0000 }

    /// `arch_def.token_bpf`: what the kernel reports in `seccomp_data.arch` (`linux/audit.h`).
    pub open spec fn matches_arch(self, arch: Arch) -> bool {
        match arch {
            Arch::X86 => self.arch == 0x4000_0003,
            Arch::X86_64 | Arch::X32 => self.arch == 0xC000_003E,
            Arch::Arm => self.arch == 0x4000_0028,
            Arch::Aarch64 => self.arch == 0xC000_00B7,
        }
    }

    /// Whether the syscall name matches the event and if it is an exact match or a multiplexed match.
    pub open spec fn matches_syscall(self, arch: Arch, name: SyscallName) -> SyscallMatch {
        if name.to_nr(arch) == Some(self.nr) {
            SyscallMatch::Exact
        } else if arch == Arch::X86 && {
            // Matching against multiplexed `socketcall` or `ipc` on x86.
            ||| Some(self.nr) == SyscallName::Socketcall.to_nr(arch)
                && name.to_socketcall_arg() == Some(self.args[0] & 0xFFFF_FFFF)
            ||| Some(self.nr) == SyscallName::Ipc.to_nr(arch)
                && name.to_ipc_arg() == Some(self.args[0] & 0xFFFF_FFFF)
        } {
            SyscallMatch::Mux
        } else {
            SyscallMatch::None
        }
    }
}

impl Arch {
    /// Mask for the syscall number and arguments, depending on the architecture word size.
    pub open spec fn mask(self) -> u64 {
        if self == Arch::X86_64 || self == Arch::Aarch64 {
            u64::MAX
        } else {
            0xFFFF_FFFF
        }
    }
}

impl ArgCmp {
    /// `_db_rule_gen_64` / `_db_rule_gen_32`.
    pub open spec fn holds(self, arch: Arch, args: Seq<u64>) -> bool {
        let x = args[self.arg as int] & arch.mask();
        let a = self.datum_a & arch.mask();
        let b = self.datum_b & arch.mask();
        match self.op {
            Compare::Ne => x != a,
            Compare::Lt => x < a,
            Compare::Le => x <= a,
            Compare::Eq => x == a,
            Compare::Ge => x >= a,
            Compare::Gt => x > a,
            Compare::MaskedEq => x & a == b & a,
        }
    }
}

impl Rule {
    /// Whether this rule matches event `ev` on `arch`.
    pub open spec fn eval(self, arch: Arch, ev: Event) -> bool {
        let conds_hold = forall |i: int| #![trigger self.conds[i]]
            0 <= i < self.conds.len() ==> self.conds[i].holds(arch, ev.args);
        match self.syscall {
            Syscall::Skip => ev.is_skip() && conds_hold,
            Syscall::Name(name) => match ev.matches_syscall(arch, name) {
                SyscallMatch::Exact => conds_hold,
                // This is stricter than libseccomp, which still evaluates the conditions on a multiplexed syscall.
                SyscallMatch::Mux => self.conds.len() == 0,
                SyscallMatch::None => false,
            },
        }
    }
}

impl Policy {
    pub open spec fn is_active_arch(self, arch: Arch, ev: Event) -> bool {
        &&& self.archs.contains(arch)
        &&& ev.matches_arch(arch)
        // Some special cases when the policy supports both X86_64 and X32.
        &&& arch == Arch::X86_64 ==> !ev.x32_bit() || ev.is_skip() || self.archs.contains(Arch::X32)
        &&& arch == Arch::X32 ==> ev.x32_bit() || self.archs.contains(Arch::X86_64)
    }

    /// Defines whether evaluating the policy on event `ev`
    /// results in the action `act`, which may not be unique.
    pub open spec fn eval(self, ev: Event, act: Action) -> bool
        recommends self.wf(),
    {
        // The event is not from an active arch.
        ||| act == self.attrs.act_badarch && forall |a: Arch| !self.is_active_arch(a, ev)
        // Exists a rule that, when evaluated on an active arch, matches the event and has the action `act`.
        ||| exists |a: Arch, i: int| {
            &&& self.is_active_arch(a, ev)
            &&& 0 <= i < self.rules.len()
            &&& #[trigger] self.rules[i].eval(a, ev)
            &&& self.rules[i].action == act
        }
        // Take the default action when no rule matches on any active arch.
        ||| {
            &&& act == self.attrs.act_default
            &&& exists |a: Arch| #[trigger] self.is_active_arch(a, ev)
            &&& forall |a: Arch, i: int|
                    self.is_active_arch(a, ev) && 0 <= i < self.rules.len()
                    ==> !#[trigger] self.rules[i].eval(a, ev)
        }
    }

    /// A policy is coherent if it never evaluates to two different actions on the same event.
    pub open spec fn coherent(self) -> bool {
        forall |ev: Event, a: Action, b: Action|
            self.eval(ev, a) && self.eval(ev, b) ==> a == b
    }
}

} // verus!
