//! Supporting witnesses and proofs for chain evaluation and compilation.

use vstd::prelude::*;
use crate::spec::cbpf::*;
use crate::spec::policy::*;

verus! {

impl Policy {
    /// The witness in the nonempty branch of `Policy::eval_chain`.
    pub(super) open spec fn chain_wins(policies: Seq<Policy>, ev: Event, act: Action, i: int) -> bool {
        &&& 0 <= i < policies.len()
        &&& policies[i].eval(ev, act)
        &&& forall |j: int, other: Action| 0 <= j < policies.len()
            && #[trigger] policies[j].eval(ev, other) ==> {
                ||| other.precedence() < act.precedence()
                ||| other.precedence() == act.precedence() && j <= i
            }
    }

    pub(super) proof fn lemma_chain_eval_witness(policies: Seq<Policy>, ev: Event, act: Action)
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

    /// Pointwise form of the compilation guarantee, after decoding the action witness.
    pub(super) proof fn lemma_eval_chain_compiled_at(
        policies: Seq<Policy>, filters: Seq<Program>, ev: Event, data: &[u8], act: Action,
    )
        requires
            policies.len() == filters.len(),
            forall |i: int| 0 <= i < policies.len() ==> #[trigger] policies[i].wf(),
            forall |i: int| 0 <= i < filters.len() ==> #[trigger] filters[i].wf(),
            forall |i: int| 0 <= i < filters.len() ==> {
                &&& #[trigger] filters[i].eval(data) matches Outcome::Return(ret)
                &&& policies[i].eval(ev, Action::from_ret(ret))
                &&& ret == Action::from_ret(ret).to_ret()
            },
        ensures Self::eval_chain(policies, ev, act)
            <==> Program::eval_chain(filters, data, act.to_ret()),
    {
        hide(Policy::eval);
        hide(Program::eval);
        act.lemma_to_ret();
        Action::Allow.lemma_to_ret();
        assert(Action::RET_ALLOW & Action::RET_ACTION == Action::RET_ALLOW) by (bit_vector);
        let ret = act.to_ret();
        Action::lemma_canonical_ret(ret);
        Action::lemma_canonical_ret(Action::RET_ALLOW);
        assert forall |j: int| 0 <= j < filters.len() implies
            Action::recognized_ret((#[trigger] filters[j].eval(data))->Return_0) by {
            Action::lemma_canonical_ret(filters[j].eval(data)->Return_0);
        }
        if policies.len() != 0 {
            if Self::eval_chain(policies, ev, act) {
                Self::lemma_chain_eval_witness(policies, ev, act);
                let i = choose |i: int| #[trigger] Self::chain_wins(policies, ev, act, i);
                let selected = filters[i].eval(data)->Return_0;
                policies[i].lemma_eval_unique(ev, act, Action::from_ret(selected));
                assert(filters[i].eval(data) == Outcome::Return(ret));
                if act == Action::Allow {
                    assert forall |j: int| 0 <= j < filters.len() implies {
                        &&& #[trigger] filters[j].eval(data) matches Outcome::Return(other)
                        &&& other & Action::RET_ACTION == Action::RET_ALLOW
                    } by {
                        let other = filters[j].eval(data)->Return_0;
                        assert(policies[j].eval(ev, Action::from_ret(other)));
                        assert(Action::from_ret(other).precedence() <= act.precedence());
                        assert(Action::from_ret(other) == Action::Allow);
                    }
                } else {
                    Action::lemma_ret_precedence(ret, Action::RET_ALLOW);
                    assert forall |j: int| 0 <= j < filters.len() implies {
                        &&& #[trigger] filters[j].eval(data) matches Outcome::Return(other)
                        &&& {
                            let priority = (ret & Action::RET_ACTION) as i32;
                            let other_priority = (other & Action::RET_ACTION) as i32;
                            priority < other_priority || (priority == other_priority && j <= i)
                        }
                    } by {
                        let other = filters[j].eval(data)->Return_0;
                        assert(policies[j].eval(ev, Action::from_ret(other)));
                        Action::lemma_ret_precedence(ret, other);
                    }
                    assert(Program::chain_wins(filters, data, ret, i));
                }
                assert(Program::eval_chain(filters, data, ret));
            }
            if Program::eval_chain(filters, data, ret) {
                if ret == Action::RET_ALLOW {
                    assert(act == Action::Allow);
                    let i = policies.len() - 1;
                    let selected = filters[i].eval(data)->Return_0;
                    assert(Action::from_ret(selected) == Action::Allow);
                    assert(policies[i].eval(ev, act));
                    assert forall |j: int, other: Action| 0 <= j < policies.len()
                        && #[trigger] policies[j].eval(ev, other) implies {
                            ||| other.precedence() < act.precedence()
                            ||| other.precedence() == act.precedence() && j <= i
                        } by {
                        let raw = filters[j].eval(data)->Return_0;
                        assert(Action::from_ret(raw) == Action::Allow);
                        policies[j].lemma_eval_unique(ev, other, Action::from_ret(raw));
                    }
                    assert(Self::chain_wins(policies, ev, act, i));
                } else {
                    Program::lemma_chain_eval_witness(filters, data, ret);
                    let i = choose |i: int| #[trigger] Program::chain_wins(filters, data, ret, i);
                    assert(policies[i].eval(ev, act));
                    assert forall |j: int, other: Action| 0 <= j < policies.len()
                        && #[trigger] policies[j].eval(ev, other) implies {
                            ||| other.precedence() < act.precedence()
                            ||| other.precedence() == act.precedence() && j <= i
                        } by {
                        let raw = filters[j].eval(data)->Return_0;
                        policies[j].lemma_eval_unique(ev, other, Action::from_ret(raw));
                        Action::lemma_ret_precedence(ret, raw);
                    }
                    assert(Self::chain_wins(policies, ev, act, i));
                }
                assert(Self::eval_chain(policies, ev, act));
            }
        }
    }
}

impl Program {
    /// The witness in the non-ALLOW branch of `Program::eval_chain`.
    pub(super) open spec fn chain_wins(filters: Seq<Program>, data: &[u8], ret: u32, i: int) -> bool {
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

    proof fn lemma_chain_eval_witness(filters: Seq<Program>, data: &[u8], ret: u32)
        requires Self::eval_chain(filters, data, ret), ret != Action::RET_ALLOW
        ensures exists |i: int| #[trigger] Self::chain_wins(filters, data, ret, i)
    {
        hide(Program::eval);
        let i = choose |i: int| {
            &&& 0 <= i < filters.len()
            &&& #[trigger] filters[i].eval(data) == Outcome::Return(ret)
            &&& ((ret & Action::RET_ACTION) as i32) < (Action::RET_ALLOW as i32)
            &&& forall |j: int| 0 <= j < filters.len() ==> {
                &&& #[trigger] filters[j].eval(data) matches Outcome::Return(other)
                &&& {
                    let priority = (ret & Action::RET_ACTION) as i32;
                    let other_priority = (other & Action::RET_ACTION) as i32;
                    priority < other_priority || (priority == other_priority && j <= i)
                }
            }
        };
        assert(Self::chain_wins(filters, data, ret, i));
    }
}

} // verus!
