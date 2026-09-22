//! The buffer a filter is assembled in, back to front.

use vstd::prelude::*;
use crate::spec::cbpf::*;
use super::CompileError;

verus! {

/// A program point of a [`Builder`], to be used as a jump target.
pub(super) type Label = usize;

/// Assembles a program *back to front* to calculate jump offets more easily.
pub(super) struct Builder {
    /// The instructions emitted so far, in reverse program order.
    pub(super) rev: Vec<Instr>,
}

impl Builder {
    pub(super) fn new() -> (res: Builder)
        ensures res.rev@.len() == 0
    {
        Builder { rev: Vec::new() }
    }

    /// The point just in front of everything emitted so far, i.e. where control
    /// arrives once the instructions emitted up to now have run to their end.
    pub(super) fn label(&self) -> (res: Label)
        ensures res == self.rev@.len()
    {
        self.rev.len()
    }

    /// Puts one instruction in front of the program.
    pub(super) fn emit(&mut self, instr: Instr)
        ensures
            Builder::extends(old(self).rev@, final(self).rev@),
            final(self).rev@ == old(self).rev@.push(instr),
            old(self).wf() && Builder::instr_ok(instr, old(self).rev@.len()) ==> final(self).wf(),
    {
        self.rev.push(instr);
    }

    /// Puts a conditional jump in front of the program: control moves to `target`
    /// when `A op src` equals `expect`, and falls through otherwise.
    ///
    /// A cBPF jump offset is a single byte, so a target further away than that is
    /// reached through a `Ja` trampoline.
    pub(super) fn emit_jump(&mut self, op: JmpOp, src: Src, expect: bool, target: Label) -> (res: Result<(), CompileError>)
        requires
            src is K,
            0 < target <= self.rev@.len(),
            self.wf(),
        ensures
            Builder::extends(old(self).rev@, final(self).rev@),
            final(self).wf(),
            res is Ok ==> forall |data: &[u8], a: u32| op.eval(a, src->K_0) == expect ==>
                #[trigger] Builder::goes_to(final(self).rev@, data, final(self).rev@.len(),
                    a, target as nat, a),
            res is Ok ==> forall |data: &[u8], a: u32| op.eval(a, src->K_0) != expect ==>
                #[trigger] Builder::goes_to(final(self).rev@, data, final(self).rev@.len(),
                    a, old(self).rev@.len(), a),
    {
        let off = self.label() - target;
        if off <= u8::MAX as usize {
            let off = off as u8;
            let jt = if expect { off } else { 0 };
            let jf = if expect { 0 } else { off };
            self.emit(Instr::Jmp { op, src, jt, jf });
            proof { Builder::lemma_jmp(self.rev@, op, src->K_0, jt, jf); }
            Ok(())
        } else if off <= u32::MAX as usize {
            //      jmp op, src     ; take the branch that leads into the trampoline
            //      ja  target
            self.emit(Instr::Ja(off as u32));
            proof { Builder::lemma_ja(self.rev@, off as u32); }
            let ghost trampoline = self.rev@;
            let jt = if expect { 0 } else { 1 };
            let jf = if expect { 1 } else { 0 };
            self.emit(Instr::Jmp { op, src, jt, jf });
            proof {
                Builder::lemma_jmp(self.rev@, op, src->K_0, jt, jf);
                assert forall |data: &[u8], a: u32| op.eval(a, src->K_0) == expect implies
                    #[trigger] Builder::goes_to(self.rev@, data, self.rev@.len(), a, target as nat, a) by {
                    Builder::lemma_then(trampoline, self.rev@, data, self.rev@.len(), a,
                        trampoline.len(), a, target as nat, a);
                }
            }
            Ok(())
        } else {
            Err(CompileError::JmpIdxOverflow)
        }
    }

    /// Reverses the buffer into a program.
    pub(super) fn finish(self) -> (res: Program)
        ensures res.instrs@ == self.rev@.reverse()
    {
        let ghost all = self.rev@;
        let mut rev = self.rev;
        let mut instrs: Vec<Instr> = Vec::new();
        while let Some(instr) = rev.pop()
            invariant
                rev@.len() <= all.len(),
                forall |j: int| #![trigger all[j]] 0 <= j < rev@.len() ==> rev@[j] == all[j],
                instrs@.len() == all.len() - rev@.len(),
                forall |j: int| #![trigger instrs@[j]]
                    0 <= j < instrs@.len() ==> instrs@[j] == all[all.len() - 1 - j],
            ensures rev@.len() == 0
            decreases rev@.len()
        {
            instrs.push(instr);
        }
        assert(instrs@ =~= all.reverse());
        Program { instrs }
    }
}

} // verus!
