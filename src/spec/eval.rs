//! Evaluation semantics of the libseccomp policy language: the verdict that the filter
//! libseccomp builds from a `Policy` gives for one syscall.

use vstd::prelude::*;
use super::policy::*;

verus! {

/// `struct seccomp_data` without the instruction pointer.
pub struct Event {
    pub arch: u32,
    pub nr: i32,
    pub args: Seq<u64>,
}

impl Event {
    /// `nr >= X32_SYSCALL_BIT` (`src/arch-x32.h`) as the BPF's unsigned comparison sees it.
    pub open spec fn x32_bit(self) -> bool { self.nr < 0 || self.nr >= 0x4000_0000 }
}

impl Arch {
    /// `arch_def.token_bpf`: what the kernel reports in `seccomp_data.arch` (`linux/audit.h`).
    pub open spec fn audit_arch(self) -> u32 {
        match self {
            Arch::X86 => 0x4000_0003,
            Arch::X86_64 | Arch::X32 => 0xC000_003E,
            Arch::Arm => 0x4000_0028,
            Arch::Aarch64 => 0xC000_00B7,
        }
    }

    /// `arch_def.size == ARCH_SIZE_64`.
    pub open spec fn is_64bit(self) -> bool { self == Arch::X86_64 || self == Arch::Aarch64 }
}

impl Syscall {
    /// `__x86_NR_socketcall`.
    pub const X86_SOCKETCALL: i32 = 102;

    /// `__x86_NR_ipc`.
    pub const X86_IPC: i32 = 117;

    /// `src/syscalls.csv` column `self`: `Some(n)` with `n >= 0` if the syscall exists there
    /// (`X32_SYSCALL_BIT` set for x32), `Some(pnr(name))` if the row says PNR, `None` if
    /// libseccomp has no row for `name`.
    pub uninterp spec fn lookup(arch: Arch, name: Seq<char>) -> Option<i32>;

    /// `include/seccomp-syscalls.h`: the `__PNR_*` constant of `name` (`<= -100`), if it has one.
    pub uninterp spec fn pnr(name: Seq<char>) -> Option<i32>;

    /// `__PNR_socket`..`__PNR_sendmmsg`
    pub open spec fn socket_family(p: i32) -> bool { -120 <= p <= -100 }

    /// `__PNR_semop`..`__PNR_shmctl`
    pub open spec fn ipc_family(p: i32) -> bool { -224 <= p <= -200 }
}

impl ArgCmp {
    /// `_db_rule_gen_64` / `_db_rule_gen_32`.
    pub open spec fn holds(self, arch: Arch, args: Seq<u64>) -> bool {
        let m: u64 = if arch.is_64bit() { u64::MAX } else { 0xFFFF_FFFF };
        let x = args[self.arg as int] & m;
        let a = self.datum_a & m;
        let b = self.datum_b & m;
        match self.op {
            Compare::Ne => x != a,
            Compare::Lt => x < a,
            Compare::Le => x <= a,
            Compare::Eq => x == a,
            Compare::Ge => x >= a,
            Compare::Gt => x > a,
            Compare::MaskedEq => (x & a) == (b & a),
        }
    }
}

impl Rule {
    pub open spec fn matches_muxed_syscall(self, arch: Arch, ev: Event) -> bool {
        &&& self.syscall matches Syscall::Name(name)
        &&& Syscall::pnr(name) matches Some(p)
        &&& {
            // Two special syscalls in X86 can be multiplexed.
            ||| arch == Arch::X86 && Syscall::socket_family(p) && ev.nr == Syscall::X86_SOCKETCALL && (ev.args[0] & 0xFFFF_FFFF) == (-p % 100) as u64
            ||| arch == Arch::X86 && Syscall::ipc_family(p) && ev.nr == Syscall::X86_IPC && (ev.args[0] & 0xFFFF_FFFF) == (-p % 200) as u64
        }
    }

    pub open spec fn matches_exact_syscall(self, arch: Arch, ev: Event) -> bool {
        match self.syscall {
            Syscall::Name(name) => ev.nr >= 0 && Syscall::lookup(arch, name) == Some(ev.nr),
            Syscall::Skip => ev.nr == -1,
        }
    }

    pub open spec fn eval(self, arch: Arch, ev: Event) -> bool {
        if self.matches_muxed_syscall(arch, ev) {
            // Ignores conditions on arg0 for muxed syscalls.
            forall |i: int| #![trigger self.conds[i]]
                0 <= i < self.conds.len() && self.conds[i].arg != 0 ==> self.conds[i].holds(arch, ev.args)
        } else if self.matches_exact_syscall(arch, ev) {
            forall |i: int| #![trigger self.conds[i]]
                0 <= i < self.conds.len() ==> self.conds[i].holds(arch, ev.args)
        } else {
            false
        }
    }
}

impl Policy {
    pub open spec fn is_active_arch(self, arch: Arch, ev: Event) -> bool {
        &&& self.archs.contains(arch)
        &&& arch.audit_arch() == ev.arch
        // Some special cases when the policy supports both X86_64 and X32.
        &&& arch == Arch::X86_64 ==> !ev.x32_bit() || ev.nr == -1 || self.archs.contains(Arch::X32)
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
        ||| exists |a: Arch, i: int|
                self.is_active_arch(a, ev) && 0 <= i < self.rules.len()
                && #[trigger] self.rules[i].eval(a, ev) && self.rules[i].action == act
        // Take the default action when no rule matches on any active arch.
        ||| act == self.attrs.act_default
                && (exists |a: Arch| #[trigger] self.is_active_arch(a, ev))
                && (forall |a: Arch, i: int|
                        self.is_active_arch(a, ev) && 0 <= i < self.rules.len()
                        ==> !#[trigger] self.rules[i].eval(a, ev))
    }

    /// A policy is coherent if it never evaluates to two different actions on the same event.
    pub open spec fn coherent(self) -> bool {
        forall |ev: Event, a: Action, b: Action|
            self.eval(ev, a) && self.eval(ev, b) ==> a == b
    }
}

} // verus!
