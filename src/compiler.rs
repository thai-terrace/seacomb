//! A simple compiler from policies to cBPF programs.
//!
//! The filter follows the shape libseccomp's does: one test per architecture the
//! policy covers, inside it one link per distinct syscall number, and inside that
//! the argument tests of the rules on that syscall.

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
        // TODO: prove.
        assume(false);

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
    fn finish(self) -> (res: Program)
        ensures res.instrs@ == self.rev@.reverse()
    {
        // TODO: prove.
        assume(false);

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
}

impl Action {
    /// The filter return value that makes the kernel take this action,
    /// i.e. the inverse of [`Action::from_ret`].
    pub fn to_ret(&self) -> (res: u32)
        ensures Action::from_ret(res) == *self
    {
        // TODO: prove; every `RET_*` constant leaves `RET_DATA` free, so the data
        // rides along in the low half without disturbing the action.
        assume(false);

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

impl Policy {
    /// `X32_SYSCALL_BIT` (`src/arch-x32.h`), as the filter's unsigned comparisons
    /// see it.
    const X32_SYSCALL_BIT: u32 = 0x4000_0000;

    /// Byte offset of `seccomp_data.nr`.
    const OFFSET_EVENT_NR: u32 = 0;

    /// Byte offset of `seccomp_data.arch`.
    const OFFSET_EVENT_ARCH: u32 = 4;

    /// Lowers the policy into a filter program.
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
        // TODO: prove.
        assume(false);

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
        ensures old(b).rev@.len() <= final(b).rev@.len()
    {
        // TODO: prove.
        assume(false);

        let end = b.label();
        b.emit(Instr::Ret(RetVal::K(self.attrs.act_default.to_ret())))?;
        self.emit_arch(b, arch)?;
        self.emit_x32_guard(b, arch, end)?;
        b.emit(Instr::LdAbs(Self::OFFSET_EVENT_NR))?;
        b.emit_jump(JmpOp::Eq, Src::K(arch.token()), false, end)?;
        b.emit(Instr::LdAbs(Self::OFFSET_EVENT_ARCH))
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
    fn emit_x32_guard(&self, b: &mut Builder, arch: Arch, end: Label) -> Result<(), CompileError>
        requires end <= b.rev@.len()
        ensures old(b).rev@.len() <= final(b).rev@.len()
    {
        // TODO: prove.
        assume(false);

        let pass = b.label();
        match arch {
            Arch::X86_64 => {
                b.emit_jump(JmpOp::Ge, Src::K(Self::X32_SYSCALL_BIT), true, end)?;
                b.emit_jump(JmpOp::Eq, Src::K(Event::SKIP_NR as u32), true, pass)
            }
            Arch::X32 => b.emit_jump(JmpOp::Ge, Src::K(Self::X32_SYSCALL_BIT), false, end),
            _ => Ok(()),
        }
    }

    /// Emits the dispatch chain of one architecture, entered with `A` holding
    /// `seccomp_data.nr` and falling through when no rule of `arch` matches the event.
    fn emit_arch(&self, b: &mut Builder, arch: Arch) -> Result<(), CompileError>
        ensures old(b).rev@.len() <= final(b).rev@.len()
    {
        // TODO: implement.
        assume(false);
        todo!()
    }
}

} // verus!
