//! Abstract syntax and semantics of the libseccomp policy/rule language.

use vstd::prelude::*;
use super::syscall::*;

// Syntax
verus! {

/// Architecture tokens `SCMP_ARCH_*` (excluding `SCMP_ARCH_NATIVE`).
#[derive(Clone, Copy, PartialEq, Eq, Structural)]
pub enum Arch { X86, X86_64, Arm, Aarch64 }

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
    pub a: u64,
    /// For MaskedEq only: `a` is the mask, `b` the value.
    pub b: u64,
}

/// One `seccomp_rule_add[_exact][_array]` call.
pub struct Rule {
    pub action: Action,
    pub syscall: Syscall,
    pub conds: Vec<ArgCmp>,
    /// `true` for the `_exact` variants (fail instead of adapting the rule per arch).
    pub exact: bool,
}

/// A whole filter context (`scmp_filter_ctx`), viewed declaratively.
pub struct Policy {
    pub archs: Vec<Arch>,
    pub rules: Vec<Rule>,
    /// Default action when the arch is supported but no rule matches.
    pub act_no_match: Action,
    /// Default action when the arch is not supported.
    pub act_bad_arch: Action,
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

    /// Higher-precedence actions override lower  ones.
    /// This behavior is similar to when we install multiple filters:
    /// <https://docs.kernel.org/userspace-api/seccomp_filter.html#return-values>.
    /// 
    /// NOTE that, e.g., `Errno(1)` and `Error(2)` are not ordered.
    pub open spec fn precedence(self) -> nat {
        match self {
            Action::KillProcess => 7,
            Action::KillThread => 6,
            Action::Trap(_) => 5,
            Action::Errno(_) => 4,
            Action::Notify => 3,
            Action::Trace(_) => 2,
            Action::Log => 1,
            Action::Allow => 0,
        }
    }
}


impl Rule {
    /// `src/arch.h`.
    pub const ARG_COUNT_MAX: u32 = 6;

    /// Conditions required to validate and compile a rule.
    pub open spec fn wf(self) -> bool {
        &&& self.action.wf()
        &&& forall |i: int| #![trigger self.conds@[i]]
                0 <= i < self.conds@.len() ==> self.conds@[i].arg < Self::ARG_COUNT_MAX
    }
}

impl Policy {
    pub open spec fn wf(self) -> bool {
        &&& self.act_no_match.wf()
        &&& self.act_bad_arch.wf()
        &&& forall |i: int, j: int| #![trigger self.archs@[i], self.archs@[j]]
                0 <= i < j < self.archs@.len() ==> self.archs@[i] != self.archs@[j]
        &&& forall |i: int| #![trigger self.rules@[i]]
                0 <= i < self.rules@.len() ==> self.rules@[i].wf()
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

impl Arch {
    // `AUDIT_ARCH_*` in `linux/audit.h`.
    pub const TOKEN_X86: u32 = 0x4000_0003;
    pub const TOKEN_X86_64: u32 = 0xC000_003E;
    pub const TOKEN_ARM: u32 = 0x4000_0028;
    pub const TOKEN_AARCH64: u32 = 0xC000_00B7;

    /// Mask for the syscall number and arguments, depending on the architecture word size.
    pub open spec fn mask(self) -> u64 {
        if self == Arch::X86_64 || self == Arch::Aarch64 {
            u64::MAX
        } else {
            0xFFFF_FFFF
        }
    }

    /// Returns the arch token reported by the kernel (`linux/audit.h`).
    pub open spec fn token(self) -> u32 {
        match self {
            Arch::X86 => Self::TOKEN_X86,
            Arch::X86_64 => Self::TOKEN_X86_64,
            Arch::Arm => Self::TOKEN_ARM,
            Arch::Aarch64 => Self::TOKEN_AARCH64,
        }
    }
}

impl Event {
    /// Whether the syscall name matches the event and if it is an exact match or a multiplexed match.
    pub open spec fn matches_syscall(self, arch: Arch, name: Syscall) -> SyscallMatch {
        if name.nr(arch) == Some(self.nr) {
            SyscallMatch::Exact
        } else if arch == Arch::X86 && {
            // Matching against multiplexed `socketcall` or `ipc` on x86.
            ||| Syscall::Socketcall.nr(arch) == Some(self.nr)
                && name.to_socketcall_arg() == Some(self.args[0] & arch.mask())
            ||| Syscall::Ipc.nr(arch) == Some(self.nr)
                && name.to_ipc_arg() == Some(self.args[0] & arch.mask())
        } {
            SyscallMatch::Mux
        } else {
            SyscallMatch::None
        }
    }

    /// Parses a (little-endian) `seccomp_data` from the kernel into an `Event`.
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
    pub const RET_ACTION: u32 = 0xffff_0000;
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
        let action = ret & Self::RET_ACTION;
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

impl ArgCmp {
    /// `_db_rule_gen_64` / `_db_rule_gen_32`.
    pub open spec fn holds(self, arch: Arch, args: Seq<u64>) -> bool {
        let x = args[self.arg as int] & arch.mask();
        let a = self.a & arch.mask();
        let b = self.b & arch.mask();
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
        match ev.matches_syscall(arch, self.syscall) {
            SyscallMatch::Exact => conds_hold,
            // This is stricter than libseccomp, which still evaluates the conditions on a multiplexed syscall.
            SyscallMatch::Mux => self.conds@.len() == 0,
            SyscallMatch::None => false,
        }
    }
}

impl Policy {
    pub open spec fn is_active_arch(self, arch: Arch, ev: Event) -> bool {
        self.archs@.contains(arch) && ev.arch == arch.token()
    }

    /// Defines whether evaluating the policy on event `ev`
    /// results in the action `act`, which may not be unique.
    pub open spec fn eval(self, ev: Event, act: Action) -> bool
        recommends self.wf(),
    {
        // The event is not from an active arch.
        ||| act == self.act_bad_arch && forall |a: Arch| !self.is_active_arch(a, ev)
        // Exists a rule that, when evaluated on an active arch, matches the event and has the action `act`.
        ||| exists |a: Arch, i: int| {
            &&& self.is_active_arch(a, ev)
            &&& 0 <= i < self.rules@.len()
            &&& #[trigger] self.rules@[i].eval(a, ev)
            &&& self.rules@[i].action == act
            // A disambiguation rule following kernel's behavior:
            // 1. Higher precedence actions win.
            // 2. If two actions have the same precedence (e.g. `Errno(1)` and `Errno(2)`),
            //    the rule that was added last wins.
            //
            // In particular, this should imply that if we install two policies consecutively:
            // ```
            // policy1.install();
            // policy2.install();
            // ```
            // then the resulting behavior is equivalent to installing `policy1 + policy2` once.
            // (assuming other equal flags).
            &&& forall |j: int| #![trigger self.rules@[j]]
                    0 <= j < self.rules@.len() && j != i && self.rules@[j].eval(a, ev)
                    ==> {
                        ||| self.rules@[j].action.precedence() < act.precedence()
                        ||| j < i && self.rules@[j].action.precedence() == act.precedence()
                    }
        }
        // Take the default action when no rule matches on any active arch.
        ||| {
            &&& act == self.act_no_match
            &&& exists |a: Arch| #[trigger] self.is_active_arch(a, ev)
            &&& forall |a: Arch, i: int|
                    self.is_active_arch(a, ev) && 0 <= i < self.rules@.len()
                    ==> !#[trigger] self.rules@[i].eval(a, ev)
        }
    }
}

} // verus!
