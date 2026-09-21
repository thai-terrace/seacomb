//! Abstract syntax and semantics of the libseccomp policy/rule language.

use vstd::prelude::*;
pub use super::syscall::*;

verus! {

/// Architecture tokens `SCMP_ARCH_*` (excluding `SCMP_ARCH_NATIVE`).
#[derive(Clone, Copy, PartialEq, Eq, Structural)]
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
    pub conds: Vec<ArgCmp>,
    /// `true` for the `_exact` variants (fail instead of adapting the rule per arch).
    pub exact: bool,
}

/// Filter attributes, `enum scmp_filter_attr` (`struct db_filter_attr`).
pub struct Attrs {
    /// Default action when no rule matches.
    pub act_default: Action,
    /// Default action when the syscall's architecture is not supported by the policy.
    pub act_badarch: Action,
    /// Set `no_new_privs` before installing the filter.
    pub ctl_nnp: bool,
    /// Synchronize the installed filter across all threads.
    pub ctl_tsync: bool,
    /// Allow rules for syscall number -1 (`Syscall::Skip`).
    pub api_tskip: bool,
    /// Request logging of all filter actions except `Allow`.
    pub ctl_log: bool,
    /// Disable speculative store bypass mitigations.
    pub ctl_ssb: bool,
    /// Select raw system error reporting; currently ignored.
    pub api_sysrawrc: bool,
    /// Request wait-killable notification semantics; currently ignored.
    pub ctl_waitkill: bool,
}

/// A whole filter context (`scmp_filter_ctx`), viewed declaratively.
pub struct Policy {
    pub attrs: Attrs,
    pub archs: Vec<Arch>,
    pub rules: Vec<Rule>,
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

    /// Conditions required to validate and compile a rule.
    pub open spec fn wf(self, attrs: Attrs) -> bool {
        &&& self.action.wf()
        &&& self.action != attrs.act_default
        &&& self.syscall.wf(attrs.api_tskip)
        &&& forall |i: int| #![trigger self.conds@[i]]
                0 <= i < self.conds@.len() ==> self.conds@[i].arg < Self::ARG_COUNT_MAX
    }
}

impl Policy {
    /// `db_col_db_add`: no duplicate arch (-EEXIST).
    pub open spec fn archs_wf(self) -> bool {
        forall |i: int, j: int| #![trigger self.archs@[i], self.archs@[j]]
            0 <= i < j < self.archs@.len() ==> self.archs@[i] != self.archs@[j]
    }

    pub open spec fn wf(self) -> bool {
        &&& self.attrs.act_default.wf()
        &&& self.attrs.act_badarch.wf()
        &&& self.archs_wf()
        &&& forall |i: int| #![trigger self.rules@[i]]
                0 <= i < self.rules@.len() ==> self.rules@[i].wf(self.attrs)
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
        if name.nr(arch) == Some(self.nr) {
            SyscallMatch::Exact
        } else if arch == Arch::X86 && {
            // Matching against multiplexed `socketcall` or `ipc` on x86.
            ||| Some(self.nr) == SyscallName::Socketcall.nr(arch)
                && name.to_socketcall_arg() == Some(self.args[0] & 0xFFFF_FFFF)
            ||| Some(self.nr) == SyscallName::Ipc.nr(arch)
                && name.to_ipc_arg() == Some(self.args[0] & 0xFFFF_FFFF)
        } {
            SyscallMatch::Mux
        } else {
            SyscallMatch::None
        }
    }

    /// Parses a (little-endian) `seccomp_data` from the kernel into an `Event`.
    /// TODO: Use Vest.
    pub open spec fn parse(data: &[u8]) -> Option<Event> {
        if data@.len() != 64 {
            None
        } else {
            Some(Event {
                nr: ((data@[0] as u32) | (data@[1] as u32) << 8 | (data@[2] as u32) << 16 | (data@[3] as u32) << 24) as i32,
                arch: (data@[4] as u32) | (data@[5] as u32) << 8 | (data@[6] as u32) << 16 | (data@[7] as u32) << 24,
                // Offset 8 is `instruction_pointer`, which `Event` drops.
                args: Seq::new(
                    Rule::ARG_COUNT_MAX as nat,
                    |k: int| (data@[16 + 8 * k] as u64)
                        | (data@[17 + 8 * k] as u64) << 8
                        | (data@[18 + 8 * k] as u64) << 16
                        | (data@[19 + 8 * k] as u64) << 24
                        | (data@[20 + 8 * k] as u64) << 32
                        | (data@[21 + 8 * k] as u64) << 40
                        | (data@[22 + 8 * k] as u64) << 48
                        | (data@[23 + 8 * k] as u64) << 56,
                ),
            })
        }
    }
}

impl Action {
    pub const RET_ACTION_FULL: u32 = 0xffff_0000;
    pub const RET_DATA: u32 = 0x0000_ffff;
    pub const RET_KILL_PROCESS: u32 = 0x8000_0000;
    pub const RET_KILL_THREAD: u32 = 0x0000_0000;
    pub const RET_TRAP: u32 = 0x0003_0000;
    pub const RET_ERRNO: u32 = 0x0005_0000;
    pub const RET_USER_NOTIF: u32 = 0x7fc0_0000;
    pub const RET_TRACE: u32 = 0x7ff0_0000;
    pub const RET_LOG: u32 = 0x7ffc_0000;
    pub const RET_ALLOW: u32 = 0x7fff_0000;

    /// Converts a BPF filter return value back to `Action`.
    pub open spec fn from_ret(ret: u32) -> Action {
        let action = ret & Self::RET_ACTION_FULL;
        let data = (ret & Self::RET_DATA) as u16;
        if action == Self::RET_ALLOW {
            Action::Allow
        } else if action == Self::RET_LOG {
            Action::Log
        } else if action == Self::RET_USER_NOTIF {
            Action::Notify
        } else if action == Self::RET_TRACE {
            Action::Trace(data)
        } else if action == Self::RET_ERRNO {
            Action::Errno(data)
        } else if action == Self::RET_TRAP {
            Action::Trap(data)
        } else if action == Self::RET_KILL_THREAD {
            Action::KillThread
        } else {
            // RET_KILL_PROCESS and every other action value.
            Action::KillProcess
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
        let conds_hold = forall |i: int| #![trigger self.conds@[i]]
            0 <= i < self.conds@.len() ==> self.conds@[i].holds(arch, ev.args);
        match self.syscall {
            Syscall::Skip => ev.is_skip() && conds_hold,
            Syscall::Name(name) => match ev.matches_syscall(arch, name) {
                SyscallMatch::Exact => conds_hold,
                // This is stricter than libseccomp, which still evaluates the conditions on a multiplexed syscall.
                SyscallMatch::Mux => self.conds@.len() == 0,
                SyscallMatch::None => false,
            },
        }
    }
}

impl Policy {
    pub open spec fn is_active_arch(self, arch: Arch, ev: Event) -> bool {
        &&& self.archs@.contains(arch)
        &&& ev.matches_arch(arch)
        // Only x32 claims the skip pseudo-syscall when the policy covers both, since its
        // rule costs fewer chain nodes and so outranks x86_64's in `db_rule_add`.
        &&& arch == Arch::X86_64 ==> !ev.x32_bit() || (ev.is_skip() && !self.archs@.contains(Arch::X32))
        &&& arch == Arch::X32 ==> ev.x32_bit()
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
            &&& 0 <= i < self.rules@.len()
            &&& #[trigger] self.rules@[i].eval(a, ev)
            &&& self.rules@[i].action == act
        }
        // Take the default action when no rule matches on any active arch.
        ||| {
            &&& act == self.attrs.act_default
            &&& exists |a: Arch| #[trigger] self.is_active_arch(a, ev)
            &&& forall |a: Arch, i: int|
                    self.is_active_arch(a, ev) && 0 <= i < self.rules@.len()
                    ==> !#[trigger] self.rules@[i].eval(a, ev)
        }
    }

    /// A policy is coherent if it never evaluates to two different actions on the same event.
    pub open spec fn coherent(self) -> bool {
        forall |ev: Event, a: Action, b: Action|
            self.eval(ev, a) && self.eval(ev, b) ==> a == b
    }
}

} // verus!
