//! A simple compiler from policies to cBPF programs.
//!
//! The filter follows the shape libseccomp's does: one test per architecture the
//! policy covers, inside it one test per rule, and inside that the rule's own
//! argument tests.

use vstd::prelude::*;
use crate::spec::{policy::*, cbpf::*};

verus! {

pub enum CompileError {
    PolicyTooLarge,
}

/// A program point of a [`Builder`], to be used as a jump target.
pub type Label = usize;

/// Assembles a program *back to front* to calculate jump offets more easily.
struct Builder {
    /// The instructions emitted so far, in reverse program order.
    rev: Vec<Instr>,
}

impl Builder {
    fn new() -> (res: Builder)
        ensures res.rev@.len() == 0
    {
        Builder { rev: Vec::new() }
    }

    /// The point just in front of everything emitted so far, i.e. where control
    /// arrives once the instructions emitted up to now have run to their end.
    fn label(&self) -> (res: Label)
        ensures res == self.rev@.len()
    {
        self.rev.len()
    }

    /// Puts one instruction in front of the program.
    fn emit(&mut self, instr: Instr) -> (res: Result<(), CompileError>)
        ensures
            old(self).rev@.len() <= final(self).rev@.len(),
            res is Ok ==> final(self).rev@ == old(self).rev@.push(instr),
            res is Err ==> *final(self) == *old(self),
    {
        if self.rev.len() >= Program::MAX_INSTRS as usize {
            return Err(CompileError::PolicyTooLarge);
        }
        self.rev.push(instr);
        Ok(())
    }

    /// Puts a conditional jump in front of the program: control moves to `target`
    /// when `A op src` equals `expect`, and falls through otherwise.
    ///
    /// A cBPF jump offset is a single byte, so a target further away than that is
    /// reached through a `Ja` trampoline.
    fn emit_jump(&mut self, op: JmpOp, src: Src, expect: bool, target: Label) -> Result<(), CompileError>
        requires target <= self.rev@.len()
        ensures old(self).rev@.len() <= final(self).rev@.len()
    {
        let off = self.label() - target;
        if off <= u8::MAX as usize {
            let off = off as u8;
            let jt = if expect { off } else { 0 };
            let jf = if expect { 0 } else { off };
            self.emit(Instr::Jmp { op, src, jt, jf })
        } else if off <= u32::MAX as usize {
            //      jmp op, src     ; take the branch that leads into the trampoline
            //      ja  target
            self.emit(Instr::Ja(off as u32))?;
            let jt = if expect { 0 } else { 1 };
            let jf = if expect { 1 } else { 0 };
            self.emit(Instr::Jmp { op, src, jt, jf })
        } else {
            Err(CompileError::PolicyTooLarge)
        }
    }

    /// Reverses the buffer into a program.
    #[verifier::external_body]
    fn finish(self) -> (res: Program)
        ensures res.instrs@ == self.rev@.reverse()
    {
        let mut rev = self.rev;
        let mut instrs: Vec<Instr> = Vec::new();
        while let Some(instr) = rev.pop()
            decreases rev@.len()
        {
            instrs.push(instr);
        }
        Program { instrs }
    }
}

impl Arch {
    /// `AUDIT_ARCH_*` in `linux/audit.h`: what the kernel reports in
    /// `seccomp_data.arch`. x86_64 and x32 are one and the same token.
    pub const TOKEN_X86: u32 = 0x4000_0003;
    pub const TOKEN_X86_64: u32 = 0xC000_003E;
    pub const TOKEN_ARM: u32 = 0x4000_0028;
    pub const TOKEN_AARCH64: u32 = 0xC000_00B7;

    /// `X32_SYSCALL_BIT` (`src/arch-x32.h`), as the filter's unsigned comparisons
    /// see it.
    const X32_SYSCALL_BIT: u32 = 0x4000_0000;

    /// Executable version of [`Event::matches_arch`].
    pub fn token(self) -> (res: u32)
        ensures forall |ev: Event| #[trigger] ev.matches_arch(self) <==> ev.arch == res
    {
        match self {
            Arch::X86 => Self::TOKEN_X86,
            Arch::X86_64 | Arch::X32 => Self::TOKEN_X86_64,
            Arch::Arm => Self::TOKEN_ARM,
            Arch::Aarch64 => Self::TOKEN_AARCH64,
        }
    }

    /// Executable version of [`Arch::mask`], which only ever says 32 or 64 bits.
    fn is_64bit(self) -> (res: bool)
        ensures res == (self.mask() == u64::MAX)
    {
        self == Arch::X86_64 || self == Arch::Aarch64
    }

    /// Emits the guard that tells apart the x86_64 and x32 syscalls.
    ///
    /// ```text
    ///     jeq #-1              -> dispatch   ; x86_64: the skip pseudo-syscall carries
    ///     jge #X32_SYSCALL_BIT -> end        ;   the bit but stays in scope
    /// ```
    /// ```text
    ///     jlt #X32_SYSCALL_BIT -> end        ; x32
    /// ```
    fn emit_x32_guard(self, b: &mut Builder, end: Label) -> Result<(), CompileError>
        requires end <= b.rev@.len()
        ensures old(b).rev@.len() <= final(b).rev@.len()
    {
        let pass = b.label();
        match self {
            Arch::X86_64 => {
                b.emit_jump(JmpOp::Ge, Src::K(Self::X32_SYSCALL_BIT), true, end)?;
                b.emit_jump(JmpOp::Eq, Src::K(Event::SKIP_NR as u32), true, pass)
            }
            Arch::X32 => b.emit_jump(JmpOp::Ge, Src::K(Self::X32_SYSCALL_BIT), false, end),
            _ => Ok(()),
        }
    }
}

impl SyscallName {
    /// Executable version of [`SyscallName::to_socketcall_arg`].
    pub fn socketcall_arg(&self) -> (res: Option<u64>)
        ensures res == self.to_socketcall_arg()
    {
        match self {
            SyscallName::Socket       => Some(1),
            SyscallName::Bind         => Some(2),
            SyscallName::Connect      => Some(3),
            SyscallName::Listen       => Some(4),
            SyscallName::Accept       => Some(5),
            SyscallName::Getsockname  => Some(6),
            SyscallName::Getpeername  => Some(7),
            SyscallName::Socketpair   => Some(8),
            SyscallName::Send         => Some(9),
            SyscallName::Recv         => Some(10),
            SyscallName::Sendto       => Some(11),
            SyscallName::Recvfrom     => Some(12),
            SyscallName::Shutdown     => Some(13),
            SyscallName::Setsockopt   => Some(14),
            SyscallName::Getsockopt   => Some(15),
            SyscallName::Sendmsg      => Some(16),
            SyscallName::Recvmsg      => Some(17),
            SyscallName::Accept4      => Some(18),
            SyscallName::Recvmmsg     => Some(19),
            SyscallName::Sendmmsg     => Some(20),
            _ => None,
        }
    }

    /// Executable version of [`SyscallName::to_ipc_arg`].
    pub fn ipc_arg(&self) -> (res: Option<u64>)
        ensures res == self.to_ipc_arg()
    {
        match self {
            SyscallName::Semop        => Some(1),
            SyscallName::Semget       => Some(2),
            SyscallName::Semctl       => Some(3),
            SyscallName::Semtimedop   => Some(4),
            SyscallName::Msgsnd       => Some(11),
            SyscallName::Msgrcv       => Some(12),
            SyscallName::Msgget       => Some(13),
            SyscallName::Msgctl       => Some(14),
            SyscallName::Shmat        => Some(21),
            SyscallName::Shmdt        => Some(22),
            SyscallName::Shmget       => Some(23),
            SyscallName::Shmctl       => Some(24),
            _ => None,
        }
    }
}

impl Action {
    /// The filter return value that makes the kernel take this action,
    /// i.e. the inverse of [`Action::from_ret`].
    #[verifier::external_body]
    pub fn to_ret(&self) -> (res: u32)
        ensures Action::from_ret(res) == *self
    {
        match self {
            Action::KillProcess => Self::RET_KILL_PROCESS,
            Action::KillThread => Self::RET_KILL_THREAD,
            Action::Trap(data) => Self::RET_TRAP | *data as u32,
            Action::Errno(data) => Self::RET_ERRNO | *data as u32,
            Action::Trace(data) => Self::RET_TRACE | *data as u32,
            Action::Log => Self::RET_LOG,
            Action::Allow => Self::RET_ALLOW,
            Action::Notify => Self::RET_USER_NOTIF,
        }
    }
}

impl Syscall {
    /// The syscall number at which `arch` reaches this syscall, as the filter's
    /// unsigned comparisons see it, if it reaches it at all.
    fn nr(&self, arch: Arch) -> Option<u32> {
        match self {
            Syscall::Skip => Some(Event::SKIP_NR as u32),
            Syscall::Name(name) => match name.nr(arch) {
                Some(nr) => Some(nr as u32),
                None => None,
            },
        }
    }
}

impl ArgCmp {
    /// Emits this test of one argument, jumping to `fail` when it does not hold and
    /// falling through when it does.
    ///
    /// A 64-bit architecture takes two words per argument, and cBPF compares one word
    /// at a time, so an ordering test there settles on the high word unless the two
    /// are equal.
    fn emit(&self, b: &mut Builder, arch: Arch, fail: Label) -> Result<(), CompileError>
        requires
            self.arg < Rule::ARG_COUNT_MAX,
            fail <= b.rev@.len(),
        ensures old(b).rev@.len() <= final(b).rev@.len()
    {
        let pass = b.label();
        let lo = Policy::OFFSET_EVENT_ARGS + 8 * self.arg;
        let hi = lo + 4;
        let a_lo = self.datum_a as u32;
        let a_hi = (self.datum_a >> 32) as u32;
        let b_lo = self.datum_b as u32;
        let b_hi = (self.datum_b >> 32) as u32;

        if !arch.is_64bit() {
            match self.op {
                Compare::Ne => b.emit_jump(JmpOp::Eq, Src::K(a_lo), true, fail)?,
                Compare::Eq => b.emit_jump(JmpOp::Eq, Src::K(a_lo), false, fail)?,
                Compare::Lt => b.emit_jump(JmpOp::Ge, Src::K(a_lo), true, fail)?,
                Compare::Le => b.emit_jump(JmpOp::Gt, Src::K(a_lo), true, fail)?,
                Compare::Ge => b.emit_jump(JmpOp::Ge, Src::K(a_lo), false, fail)?,
                Compare::Gt => b.emit_jump(JmpOp::Gt, Src::K(a_lo), false, fail)?,
                Compare::MaskedEq => {
                    b.emit_jump(JmpOp::Eq, Src::K(b_lo & a_lo), false, fail)?;
                    b.emit(Instr::Alu(AluOp::And, Src::K(a_lo)))?;
                }
            }
            return b.emit(Instr::LdAbs(lo));
        }

        match self.op {
            Compare::Eq => {
                b.emit_jump(JmpOp::Eq, Src::K(a_lo), false, fail)?;
                b.emit(Instr::LdAbs(lo))?;
                b.emit_jump(JmpOp::Eq, Src::K(a_hi), false, fail)?;
            }
            Compare::Ne => {
                b.emit_jump(JmpOp::Eq, Src::K(a_lo), true, fail)?;
                b.emit(Instr::LdAbs(lo))?;
                b.emit_jump(JmpOp::Eq, Src::K(a_hi), false, pass)?;
            }
            Compare::Lt => {
                b.emit_jump(JmpOp::Ge, Src::K(a_lo), true, fail)?;
                b.emit(Instr::LdAbs(lo))?;
                b.emit_jump(JmpOp::Eq, Src::K(a_hi), false, pass)?;
                b.emit_jump(JmpOp::Gt, Src::K(a_hi), true, fail)?;
            }
            Compare::Le => {
                b.emit_jump(JmpOp::Gt, Src::K(a_lo), true, fail)?;
                b.emit(Instr::LdAbs(lo))?;
                b.emit_jump(JmpOp::Eq, Src::K(a_hi), false, pass)?;
                b.emit_jump(JmpOp::Gt, Src::K(a_hi), true, fail)?;
            }
            Compare::Gt => {
                b.emit_jump(JmpOp::Gt, Src::K(a_lo), false, fail)?;
                b.emit(Instr::LdAbs(lo))?;
                b.emit_jump(JmpOp::Eq, Src::K(a_hi), false, fail)?;
                b.emit_jump(JmpOp::Gt, Src::K(a_hi), true, pass)?;
            }
            Compare::Ge => {
                b.emit_jump(JmpOp::Ge, Src::K(a_lo), false, fail)?;
                b.emit(Instr::LdAbs(lo))?;
                b.emit_jump(JmpOp::Eq, Src::K(a_hi), false, fail)?;
                b.emit_jump(JmpOp::Gt, Src::K(a_hi), true, pass)?;
            }
            Compare::MaskedEq => {
                b.emit_jump(JmpOp::Eq, Src::K(b_lo & a_lo), false, fail)?;
                b.emit(Instr::Alu(AluOp::And, Src::K(a_lo)))?;
                b.emit(Instr::LdAbs(lo))?;
                b.emit_jump(JmpOp::Eq, Src::K(b_hi & a_hi), false, fail)?;
                b.emit(Instr::Alu(AluOp::And, Src::K(a_hi)))?;
            }
        }
        b.emit(Instr::LdAbs(hi))
    }
}

impl Rule {
    /// Emits the test that reaches this rule at syscall number `nr`, and the rule's
    /// body under it.
    ///
    /// Forward layout, entered with `A` holding `seccomp_data.nr`:
    ///
    /// ```text
    ///     jne #nr -> end
    ///     <body>
    ///     ld  [nr]            ; hands A back to the test behind this one
    /// end:
    /// ```
    fn emit(&self, b: &mut Builder, arch: Arch, nr: u32, a_live: bool) -> Result<(), CompileError>
        requires self.conds_wf()
        ensures old(b).rev@.len() <= final(b).rev@.len()
    {
        let end = b.label();
        if a_live {
            b.emit(Instr::LdAbs(Policy::OFFSET_EVENT_NR))?;
        }
        self.emit_body(b, arch, nr)?;
        b.emit_jump(JmpOp::Eq, Src::K(nr), false, end)
    }

    /// Emits whatever this rule tests beyond the syscall number, then its action.
    ///
    /// Forward layout, with `end` just past the body:
    ///
    /// ```text
    ///     <test of one argument> -> end
    ///     ...
    ///     ret #action
    /// end:
    /// ```
    /// Reached through a multiplexer, the rule's own syscall is what the multiplexer
    /// selects on, and that selector is the only test:
    /// ```text
    ///     ld  [arg 0]
    ///     jne #selector -> end
    ///     ret #action
    /// end:
    /// ```
    fn emit_body(&self, b: &mut Builder, arch: Arch, nr: u32) -> Result<(), CompileError>
        requires self.conds_wf()
        ensures old(b).rev@.len() <= final(b).rev@.len()
    {
        let end = b.label();
        b.emit(Instr::Ret(RetVal::K(self.action.to_ret())))?;

        if let Some(arg) = self.mux_arg(arch) {
            if self.mux_nr(arch) == Some(nr) {
                b.emit_jump(JmpOp::Eq, Src::K(arg), false, end)?;
                return b.emit(Instr::LdAbs(Policy::OFFSET_EVENT_ARGS));
            }
        }

        let mut i = self.conds.len();
        while i > 0
            invariant
                i <= self.conds@.len(),
                self.conds_wf(),
                end <= b.rev@.len(),
                old(b).rev@.len() <= b.rev@.len(),
            decreases i
        {
            i -= 1;
            self.conds[i].emit(b, arch, end)?;
        }
        Ok(())
    }

    /// The call number the x86 multiplexer selects this rule's syscall on, if one
    /// reaches it.
    fn mux_arg(&self, arch: Arch) -> Option<u32> {
        if arch != Arch::X86 || self.conds.len() > 0 {
            return None;
        }
        match &self.syscall {
            Syscall::Skip => None,
            Syscall::Name(name) => match name.socketcall_arg() {
                Some(arg) => Some(arg as u32),
                None => match name.ipc_arg() {
                    Some(arg) => Some(arg as u32),
                    None => None,
                },
            },
        }
    }

    /// The number of the x86 multiplexer that also reaches this rule, if one does.
    fn mux_nr(&self, arch: Arch) -> Option<u32> {
        // `Rule::eval` takes a multiplexed match only for a rule that tests no argument.
        if arch != Arch::X86 || self.conds.len() > 0 {
            return None;
        }
        let mux = match &self.syscall {
            Syscall::Skip => None,
            Syscall::Name(name) =>
                if name.socketcall_arg().is_some() {
                    Some(SyscallName::Socketcall)
                } else if name.ipc_arg().is_some() {
                    Some(SyscallName::Ipc)
                } else {
                    None
                },
        };
        match mux {
            Some(name) => match name.nr(arch) {
                Some(nr) => Some(nr as u32),
                None => None,
            },
            None => None,
        }
    }
}

impl Policy {
    /// Byte offset of `seccomp_data.nr`.
    const OFFSET_EVENT_NR: u32 = 0;

    /// Byte offset of `seccomp_data.arch`.
    const OFFSET_EVENT_ARCH: u32 = 4;

    /// Byte offset of the low half of `seccomp_data.args[0]`.
    const OFFSET_EVENT_ARGS: u32 = 16;

    /// Lowers the policy into a filter program.
    #[verifier::external_body]
    pub fn lower(&self) -> (res: Result<Program, CompileError>)
        requires self.wf()
        ensures res matches Ok(prog) ==>
            // Compiled program is well-formed.
            prog.wf() &&
            // Compiled program runs error-free and produces an action accepted by the policy.
            forall |data: &[u8]| #[trigger] Event::parse(data) matches Some(ev) ==> {
                &&& prog.eval(data) matches Outcome::Return(ret)
                &&& self.eval(ev, Action::from_ret(ret))
            }
    {
        let mut b = Builder::new();

        // The filter's last resort: the event came from an architecture that the
        // policy leaves out of scope.
        //
        //      ret #act_badarch
        b.emit(Instr::Ret(RetVal::K(self.attrs.act_badarch.to_ret())))?;

        // One block per architecture, tried in turn:
        //
        //      <block of the first architecture>
        //      <block of the second architecture>
        //      ...
        let mut i = self.archs.len();
        while i > 0
            invariant i <= self.archs@.len()
            decreases i
        {
            i -= 1;
            self.emit_arch_block(&mut b, self.archs[i])?;
        }

        Ok(b.finish())
    }

    /// Emits the block handling `arch`.
    ///
    /// Forward layout:
    ///
    /// ```text
    ///     ld  [arch]
    ///     jne #token -> end
    ///     ld  [nr]
    ///     <x32 bit guard> -> end      ; only where one is needed
    ///     <dispatch of arch>
    ///     ret #act_default
    /// end:
    /// ```
    fn emit_arch_block(&self, b: &mut Builder, arch: Arch) -> Result<(), CompileError>
        requires self.wf()
        ensures old(b).rev@.len() <= final(b).rev@.len()
    {
        let end = b.label();
        b.emit(Instr::Ret(RetVal::K(self.attrs.act_default.to_ret())))?;
        self.emit_arch(b, arch)?;
        arch.emit_x32_guard(b, end)?;
        b.emit(Instr::LdAbs(Self::OFFSET_EVENT_NR))?;
        b.emit_jump(JmpOp::Eq, Src::K(arch.token()), false, end)?;
        b.emit(Instr::LdAbs(Self::OFFSET_EVENT_ARCH))
    }

    /// Emits the dispatch of one architecture, entered with `A` holding
    /// `seccomp_data.nr` and falling through when no rule of `arch` matches the event.
    fn emit_arch(&self, b: &mut Builder, arch: Arch) -> Result<(), CompileError>
        requires self.wf()
        ensures old(b).rev@.len() <= final(b).rev@.len()
    {
        // One test per rule, in the policy's order. Only the last of them falls through
        // to the block's default return, so every earlier one has to hand `A` back.
        let mut a_live = false;
        let mut i = self.rules.len();
        while i > 0
            invariant
                i <= self.rules@.len(),
                self.wf(),
                old(b).rev@.len() <= b.rev@.len(),
            decreases i
        {
            i -= 1;
            assert(self.rules@[i as int].wf(self.attrs));

            // x86 reaches some rules a second time through the socketcall or ipc
            // multiplexer, which answers to a number of its own.
            if let Some(nr) = self.rules[i].mux_nr(arch) {
                self.rules[i].emit(b, arch, nr, a_live)?;
                a_live = true;
            }
            if let Some(nr) = self.rules[i].syscall.nr(arch) {
                self.rules[i].emit(b, arch, nr, a_live)?;
                a_live = true;
            }
        }
        Ok(())
    }
}

} // verus!
