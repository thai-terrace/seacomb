//! Some formally verified properties about the semantics of policies and cBPF.

use vstd::prelude::*;
use crate::spec::cbpf::*;
use crate::spec::policy::*;

verus! {

impl Policy {
    /// Whether this policy accepts an action for the event.
    pub closed spec fn eval_defined(self, ev: Event) -> bool {
        exists |act: Action| self.eval(ev, act)
    }

    /// Although defined as a relation, the evaluation of a policy is a function of the event.
    pub proof fn theorem_eval_functional(self)
        requires self.wf()
        ensures
            forall |ev: Event, act1: Action, act2: Action| self.eval(ev, act1) && self.eval(ev, act2) ==> act1 == act2,
            forall |ev: Event| #[trigger] self.eval_defined(ev),
    {
        assert forall |ev: Event| #[trigger] self.eval_defined(ev) by {
            self.lemma_blocks(ev, 0);
            assert(self.eval(ev, self.blocks(ev, 0)));
        }
        assert forall |ev: Event, act1: Action, act2: Action|
            self.eval(ev, act1) && self.eval(ev, act2) implies act1 == act2 by {
            self.lemma_eval_unique(ev, act1, act2);
        }
    }

    /// A chain of well-formed policies admits at most one action for a given event.
    pub proof fn theorem_eval_chain_functional(policies: Seq<Policy>, ev: Event)
        requires forall |i: int| 0 <= i < policies.len() ==> #[trigger] policies[i].wf()
        ensures forall |a: Action, b: Action|
            Self::eval_chain(policies, ev, a) && Self::eval_chain(policies, ev, b) ==> a == b
    {
        hide(Policy::eval);
        assert forall |a: Action, b: Action|
            Self::eval_chain(policies, ev, a) && Self::eval_chain(policies, ev, b) implies a == b by {
            if policies.len() != 0 {
                Self::lemma_chain_eval_witness(policies, ev, a);
                Self::lemma_chain_eval_witness(policies, ev, b);
                let i = choose |i: int| #[trigger] Self::chain_wins(policies, ev, a, i);
                let j = choose |j: int| #[trigger] Self::chain_wins(policies, ev, b, j);
                assert(i == j);
                policies[i].lemma_eval_unique(ev, a, b);
            }
        }
    }

    /// The witness in the nonempty branch of `Policy::eval_chain`.
    spec fn chain_wins(policies: Seq<Policy>, ev: Event, act: Action, i: int) -> bool {
        &&& 0 <= i < policies.len()
        &&& policies[i].eval(ev, act)
        &&& forall |j: int, other: Action| 0 <= j < policies.len()
            && #[trigger] policies[j].eval(ev, other) ==> {
                ||| other.precedence() < act.precedence()
                ||| other.precedence() == act.precedence() && j <= i
            }
    }

    proof fn lemma_chain_eval_witness(policies: Seq<Policy>, ev: Event, act: Action)
        requires policies.len() != 0, Self::eval_chain(policies, ev, act)
        ensures exists |i: int| #[trigger] Self::chain_wins(policies, ev, act, i)
    {
        hide(Policy::eval);
        let i = choose |i: int| {
            &&& 0 <= i < policies.len()
            &&& #[trigger] policies[i].eval(ev, act)
            &&& forall |j: int, other: Action| 0 <= j < policies.len()
                && #[trigger] policies[j].eval(ev, other) ==> {
                    ||| other.precedence() < act.precedence()
                    ||| other.precedence() == act.precedence() && j <= i
                }
        };
        assert(Self::chain_wins(policies, ev, act, i));
    }

    /// Whether this rule is the ordered match selected for the event.
    spec fn wins(self, ev: Event, a: Arch, i: int) -> bool {
        &&& self.is_active_arch(a, ev)
        &&& 0 <= i < self.rules@.len()
        &&& self.rules@[i].eval(a, ev)
        &&& forall |j: int| #![trigger self.rules@[j]]
            0 <= j < self.rules@.len() && j != i && self.rules@[j].eval(a, ev) ==> {
                ||| self.rules@[j].action.precedence() < self.rules@[i].action.precedence()
                ||| j < i && self.rules@[j].action.precedence() == self.rules@[i].action.precedence()
            }
    }

    /// An accepted action has a winning rule whenever any active rule matches.
    proof fn lemma_eval_witness(self, ev: Event, act: Action, a: Arch, i: int)
        requires
            self.wf(), self.eval(ev, act),
            self.is_active_arch(a, ev), 0 <= i < self.rules@.len(), self.rules@[i].eval(a, ev),
        ensures exists |b: Arch, j: int| #[trigger] self.wins(ev, b, j) && self.rules@[j].action == act
    {
        let (b, j) = choose |b: Arch, j: int| {
            &&& self.is_active_arch(b, ev)
            &&& 0 <= j < self.rules@.len()
            &&& #[trigger] self.rules@[j].eval(b, ev)
            &&& self.rules@[j].action == act
            &&& forall |k: int| #![trigger self.rules@[k]]
                0 <= k < self.rules@.len() && k != j && self.rules@[k].eval(b, ev) ==> {
                    ||| self.rules@[k].action.precedence() < act.precedence()
                    ||| k < j && self.rules@[k].action.precedence() == act.precedence()
                }
        };
        assert(self.wins(ev, b, j));
    }

    /// Two accepted actions for an event are equal.
    pub(crate) proof fn lemma_eval_unique(self, ev: Event, act1: Action, act2: Action)
        requires self.wf(), self.eval(ev, act1), self.eval(ev, act2)
        ensures act1 == act2
    {
        if exists |a: Arch, i: int| self.is_active_arch(a, ev)
            && 0 <= i < self.rules@.len() && #[trigger] self.rules@[i].eval(a, ev) {
            let (a, i) = choose |a: Arch, i: int| self.is_active_arch(a, ev)
                && 0 <= i < self.rules@.len() && #[trigger] self.rules@[i].eval(a, ev);
            self.lemma_eval_witness(ev, act1, a, i);
            self.lemma_eval_witness(ev, act2, a, i);
            let (a, i) = choose |a: Arch, i: int| #[trigger] self.wins(ev, a, i) && self.rules@[i].action == act1;
            let (b, j) = choose |b: Arch, j: int| #[trigger] self.wins(ev, b, j) && self.rules@[j].action == act2;
            assert(a == b);
            assert(i == j);
        }
    }
}

impl Program {
    /// A filter chain admits at most one raw return value for a given input.
    pub proof fn theorem_eval_chain_unique(filters: Seq<Program>, data: &[u8])
        ensures forall |a: u32, b: u32|
            Self::eval_chain(filters, data, a) && Self::eval_chain(filters, data, b) ==> a == b
    {
        hide(Program::eval);
        assert forall |a: u32, b: u32|
            Self::eval_chain(filters, data, a) && Self::eval_chain(filters, data, b) implies a == b by {
            if a != Action::RET_ALLOW {
                let i = choose |i: int| #[trigger] Self::chain_wins(filters, data, a, i);
                if b != Action::RET_ALLOW {
                    let j = choose |j: int| #[trigger] Self::chain_wins(filters, data, b, j);
                    assert(i == j);
                } else {
                    assert((a & Action::RET_ACTION) == Action::RET_ALLOW);
                }
            } else if b != Action::RET_ALLOW {
                let j = choose |j: int| #[trigger] Self::chain_wins(filters, data, b, j);
                assert((b & Action::RET_ACTION) == Action::RET_ALLOW);
            }
        }
    }

    /// The witness in the non-ALLOW branch of `Program::eval_chain`.
    spec fn chain_wins(filters: Seq<Program>, data: &[u8], ret: u32, i: int) -> bool {
        &&& 0 <= i < filters.len()
        &&& filters[i].eval(data) == Outcome::Return(ret)
        &&& ((ret & Action::RET_ACTION) as i32) < (Action::RET_ALLOW as i32)
        &&& forall |j: int| 0 <= j < filters.len() ==> {
            &&& #[trigger] filters[j].eval(data) matches Outcome::Return(other)
            &&& {
                let priority = (ret & Action::RET_ACTION) as i32;
                let other_priority = (other & Action::RET_ACTION) as i32;
                priority < other_priority || (priority == other_priority && j <= i)
            }
        }
    }
}

} // verus!
