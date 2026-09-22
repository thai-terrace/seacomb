//! A simple compiler from policies to cBPF programs.

use vstd::prelude::*;
use crate::spec::{policy::*, cbpf::*};

mod block;
mod builder;
mod eval;
mod machine;
mod rule;
mod syscall;
mod words;

use builder::Builder;

verus! {

#[derive(Debug)]
pub enum CompileError {
    /// The compiled program exceeds the jump offset limit.
    JmpIdxOverflow,
}

impl Policy {
    /// Whether this policy accepts an action for the event.
    pub closed spec fn eval_defined(self, ev: Event) -> bool {
        exists |act: Action| self.eval(ev, act)
    }

    /// Every event has an action accepted by a well-formed policy.
    pub proof fn theorem_eval_total(self)
        requires self.wf()
        ensures forall |ev: Event| #[trigger] self.eval_defined(ev)
    {
        assert forall |ev: Event| #[trigger] self.eval_defined(ev) by {
            self.lemma_blocks(ev, 0);
            assert(self.eval(ev, self.blocks(ev, 0)));
        }
    }

    /// Although defined as a relation, the evaluation of a policy is a function of the event.
    pub proof fn theorem_eval_functional(self)
        requires self.wf()
        ensures
            forall |ev: Event, act1: Action, act2: Action| self.eval(ev, act1) && self.eval(ev, act2) ==> act1 == act2,
            forall |ev: Event| #[trigger] self.eval_defined(ev),
    {
        self.theorem_eval_total();
        assert forall |ev: Event, act1: Action, act2: Action|
            self.eval(ev, act1) && self.eval(ev, act2) implies act1 == act2 by {
            self.lemma_eval_unique(ev, act1, act2);
        }
    }

    /// Compiles the policy into a filter program.
    pub fn to_cbpf(&self) -> (res: Result<Program, CompileError>)
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
        //      ret #act_bad_arch
        b.emit(Instr::Ret(RetVal::K(self.act_bad_arch.to_ret())));

        proof { Builder::lemma_ret(b.rev@, self.act_bad_arch.to_ret()); }

        // One block per architecture token, tried in turn:
        //
        //      <block of the first architecture>
        //      <block of the second architecture>
        //      ...
        let mut i = self.archs.len();
        while i > 0
            invariant
                i <= self.archs@.len(),
                self.wf(),
                b.wf(),
                0 < b.rev@.len(),
                b.rev@[0] is Ret,
                forall |data: &[u8]| Event::parse(data) is Some ==>
                    #[trigger] Builder::returns_all(b.rev@, data, b.rev@.len(),
                        self.blocks(Event::of(data), i as int).to_ret()),
            decreases i
        {
            i -= 1;
            let ghost prev = b.rev@;
            let ghost i0 = i as int + 1;
            self.emit_arch_block(&mut b, self.archs[i])?;
            proof {
                assert forall |data: &[u8]| Event::parse(data) is Some implies
                    #[trigger] Builder::returns_all(b.rev@, data, b.rev@.len(),
                        self.blocks(Event::of(data), i as int).to_ret()) by {
                    assert(Builder::returns_all(prev, data, prev.len(),
                        self.blocks(Event::of(data), i0).to_ret()));
                }
            }
        }

        let ghost gb = b;
        let prog = b.finish();
        proof {
            gb.lemma_wf(prog);
            assert forall |data: &[u8]| #[trigger] Event::parse(data) is Some implies {
                &&& prog.eval(data) matches Outcome::Return(ret)
                &&& self.eval(Event::of(data), Action::from_ret(ret))
            } by {
                let act = self.blocks(Event::of(data), 0);
                prog.lemma_run(data);
                assert(prog.instrs@.len() == gb.rev@.len());
                assert(Builder::returns_all(gb.rev@, data, gb.rev@.len(), act.to_ret()));
                assert(Builder::extends(gb.rev@, gb.rev@));
                assert(Builder::returns(gb.rev@, data, gb.rev@.len(), 0, act.to_ret()));
                assert(Builder::run(gb.rev@, data, gb.rev@.len(), 0) == Outcome::Return(act.to_ret()));
                act.lemma_to_ret();
                self.lemma_blocks(Event::of(data), 0);
            }
        }
        Ok(prog)
    }
}

} // verus!
