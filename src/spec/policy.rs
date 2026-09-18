//! Abstract syntax of the libseccomp policy/rule language.

use vstd::prelude::*;

verus! {

pub const ARG_COUNT_MAX: u32 = 6; // `src/arch.h`: ARG_COUNT_MAX
pub const MAX_ERRNO: u32 = 4095;  // `src/system.h`: largest errno accepted by SCMP_ACT_ERRNO

/// Architecture tokens `SCMP_ARCH_*` (excluding `SCMP_ARCH_NATIVE`).
pub enum Arch {
    X86, X86_64, X32,
    Arm, Aarch64,
    Loongarch64,
    M68k,
    Mips, Mipsel, Mips64, Mipsel64, Mips64n32, Mipsel64n32,
    Parisc, Parisc64,
    Ppc, Ppc64, Ppc64le,
    S390, S390x,
    Riscv64,
    Sheb, Sh,
}

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
    /// `SCMP_SYS(name)` / `seccomp_syscall_resolve_name(name)`.
    Name(Seq<char>),
    /// A raw number: `>= 0` is a native-arch syscall number, `<= -100` is a
    /// `__PNR_*` pseudo-syscall number, `-1` is the tracer "skip" syscall
    /// (only meaningful with `api_tskip`); `-2 ..= -99` are reserved.
    Num(i32),
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
    /// `sys_chk_seccomp_action` (kernel-support probing aside).
    pub open spec fn wf(self) -> bool {
        match self {
            Action::Errno(e) => (e as u32) < MAX_ERRNO,
            _ => true,
        }
    }
}

impl Syscall {
    /// `_syscall_valid` in `src/api.c`: the reserved range is rejected; `-1` needs `api_tskip`.
    pub open spec fn wf(self, api_tskip: bool) -> bool {
        match self {
            Syscall::Name(_) => true,
            Syscall::Num(n) => !(-99 <= n <= -1) || (n == -1 && api_tskip),
        }
    }
}

impl Arch {
    pub open spec fn big_endian(self) -> bool {
        match self {
            Arch::M68k | Arch::Mips | Arch::Mips64 | Arch::Mips64n32 | Arch::Parisc
            | Arch::Parisc64 | Arch::Ppc | Arch::Ppc64 | Arch::S390 | Arch::S390x | Arch::Sheb => true,
            _ => false,
        }
    }
}

impl Rule {
    /// `db_col_rule_add`.
    pub open spec fn conds_wf(self) -> bool {
        &&& self.conds.len() <= ARG_COUNT_MAX as nat
        &&& forall |i: int| #![trigger self.conds[i]]
                0 <= i < self.conds.len() ==> self.conds[i].arg < ARG_COUNT_MAX
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
    /// `db_col_db_add`: no duplicate arch (-EEXIST), all arches share one endianness (-EDOM).
    pub open spec fn archs_wf(self) -> bool {
        &&& forall |i: int, j: int| #![trigger self.archs[i], self.archs[j]]
                0 <= i < j < self.archs.len() ==> self.archs[i] != self.archs[j]
        &&& forall |i: int, j: int| #![trigger self.archs[i], self.archs[j]]
                0 <= i < self.archs.len() && 0 <= j < self.archs.len()
                    ==> self.archs[i].big_endian() == self.archs[j].big_endian()
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
