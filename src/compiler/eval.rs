//! What the filter computes, told as a policy-level account of its blocks and rule tests.

use vstd::prelude::*;
use crate::spec::policy::*;

verus! {

impl Syscall {
    /// No syscall a multiplexer reaches answers to the multiplexer's own x86 number.
    pub(super) broadcast proof fn lemma_mux_nr(&self)
        ensures
            #[trigger] self.to_socketcall_arg() is Some
                ==> self.spec_nr(Arch::X86) != Self::Socketcall.spec_nr(Arch::X86),
            #[trigger] self.to_ipc_arg() is Some
                ==> self.spec_nr(Arch::X86) != Self::Ipc.spec_nr(Arch::X86),
    {
        reveal(Syscall::spec_nr);
    }

    /// The x86_64 and x32 syscall-number ranges overlap only at skip.
    pub(super) proof fn lemma_nr_ranges(self)
        ensures
            self.spec_nr(Arch::X86_64) matches Some(nr) ==> -1 <= nr < 0x4000_0000,
            self.spec_nr(Arch::X32) matches Some(nr) ==> nr == -1 || nr >= 0x4000_0000,
            (self.spec_nr(Arch::X86_64) == Some(-1i32)) <==> self == Self::Skip,
            forall |arch: Arch| #[trigger] Self::Skip.spec_nr(arch) == Some(-1i32),
    {
        reveal(Syscall::spec_nr);
    }

    /// Every x32 syscall number passes the x32 guard.
    pub(super) proof fn lemma_x32_nr(self)
        ensures self.spec_nr(Arch::X32) matches Some(nr) ==> nr < 0 || nr >= 0x4000_0000
    {
        reveal(Syscall::spec_nr);
    }
}

impl Arch {
    /// Whether the architecture's syscall-number guard lets `ev` through.
    pub(super) open spec fn admits(self, ev: Event) -> bool {
        self == Arch::X32 ==> ev.is_x32()
    }
}

impl Rule {
    /// Whether the rule's conditions from `i` on hold of `ev` on `arch`.
    pub(super) open spec fn conds_hold(self, arch: Arch, ev: Event, i: int) -> bool {
        forall |j: int| #![trigger self.conds@[j]]
            i <= j < self.conds@.len() ==> self.conds@[j].holds(arch, ev.args)
    }

    /// Whether the rule's body accepts `ev`, the test for syscall number `nr` having passed.
    pub(super) open spec fn body_holds(self, arch: Arch, nr: u32, ev: Event) -> bool {
        if self.spec_mux_nr(arch) == Some(nr) {
            self.spec_mux_arg(arch) == Some((ev.args[0] & 0xFFFF_FFFF) as u32)
        } else {
            self.conds_hold(arch, ev, 0)
        }
    }

    /// Whether the test for syscall number `nr` reaches this rule and its body accepts `ev`.
    pub(super) open spec fn matches_at(self, arch: Arch, nr: u32, ev: Event) -> bool {
        ev.nr as u32 == nr && self.body_holds(arch, nr, ev)
    }

    /// Whether either of the tests a block emits for this rule reaches it and accepts `ev`.
    pub(super) open spec fn matches(self, arch: Arch, ev: Event) -> bool {
        ||| match self.syscall.spec_bpf_nr(arch) {
                Some(nr) => self.matches_at(arch, nr, ev),
                None => false,
            }
        ||| match self.spec_mux_nr(arch) {
                Some(nr) => self.matches_at(arch, nr, ev),
                None => false,
            }
    }

    /// The tests a block emits for this rule come to the rule's own account of matching.
    pub(super) proof fn lemma_matches(self, arch: Arch, ev: Event)
        requires ev.args.len() == Rule::ARG_COUNT_MAX
        ensures self.matches(arch, ev) <==> self.eval(arch, ev)
    {
        broadcast use Syscall::lemma_mux_nr;
        ev.lemma_nr();
        // The multiplexer's call number is the low word of the first argument.
        assert(forall |x: u64| #[trigger] (x & 0xFFFF_FFFF) < 0x1_0000_0000) by (bit_vector);
    }

    /// Whether this ABI emits the rule's direct tests in the shared block.
    pub(super) open spec fn direct_enabled(self, arch: Arch, has_x32: bool) -> bool {
        !(arch == Arch::X86_64 && has_x32 && self.syscall == Syscall::Skip)
    }

    /// Whether the rule matches either ABI served by this architecture block.
    pub(super) open spec fn group_matches(self, arch: Arch, has_x32: bool, ev: Event) -> bool {
        (self.direct_enabled(arch, has_x32) && self.eval(arch, ev))
            || (arch == Arch::X86_64 && has_x32 && self.eval(Arch::X32, ev))
    }

    /// A matching x32 rule passes the architecture's syscall-number guard.
    pub(super) proof fn lemma_x32(self, ev: Event)
        ensures self.eval(Arch::X32, ev) ==> ev.is_x32()
    {
        self.syscall.lemma_x32_nr();
    }
}

impl Policy {
    /// The architecture block serving `arch`.
    pub(super) open spec fn block_arch(self, arch: Arch) -> Arch {
        if arch == Arch::X32 && self.archs@.contains(Arch::X86_64) { Arch::X86_64 } else { arch }
    }

    /// Whether the block for `arch` takes `ev` on.
    pub(super) open spec fn takes(self, arch: Arch, ev: Event) -> bool {
        self.block_arch(arch) == arch && ev.matches_arch(arch) && arch.admits(ev)
    }

    /// Whether rule `j` is included in the emitted priority buckets and rule prefix.
    pub(super) open spec fn included(self, j: int, priority: int, i: int) -> bool {
        &&& 0 <= j < self.rules@.len()
        &&& self.rules@[j].action.precedence() < priority
            || (self.rules@[j].action.precedence() == priority && j < i)
    }

    /// The highest-precedence matching rule, with later rules breaking ties.
    pub(super) open spec fn dispatch(self, arch: Arch, ev: Event, priority: int, i: int) -> Action
        decreases priority + 1, i
    {
        if priority < 0 {
            self.act_no_match
        } else if i <= 0 {
            self.dispatch(arch, ev, priority - 1, self.rules@.len() as int)
        } else if self.rules@[i - 1].action.precedence() == priority
            && self.rules@[i - 1].group_matches(arch, self.archs@.contains(Arch::X32), ev) {
            self.rules@[i - 1].action
        } else {
            self.dispatch(arch, ev, priority, i - 1)
        }
    }

    /// The action the blocks for `archs[i..]` take on `ev`.
    pub(super) open spec fn blocks(self, ev: Event, i: int) -> Action
        decreases self.archs@.len() - i
    {
        if i >= self.archs@.len() {
            self.act_bad_arch
        } else if self.takes(self.archs@[i], ev) {
            self.dispatch(self.archs@[i], ev, 8, self.rules@.len() as int)
        } else {
            self.blocks(ev, i + 1)
        }
    }

    /// Dispatch selects the greatest matching precedence and then the greatest rule index.
    pub(super) proof fn lemma_dispatch(self, arch: Arch, ev: Event, priority: int, i: int)
        requires -1 <= priority <= 8, 0 <= i <= self.rules@.len()
        ensures
            (exists |j: int| {
                &&& self.included(j, priority, i)
                &&& #[trigger] self.rules@[j].group_matches(arch, self.archs@.contains(Arch::X32), ev)
                &&& self.rules@[j].action == self.dispatch(arch, ev, priority, i)
                &&& forall |k: int| self.included(k, priority, i)
                    && #[trigger] self.rules@[k].group_matches(arch, self.archs@.contains(Arch::X32), ev) ==> {
                        &&& self.rules@[k].action.precedence() <= self.rules@[j].action.precedence()
                        &&& self.rules@[k].action.precedence() == self.rules@[j].action.precedence() ==> k <= j
                    }
            }) || (self.dispatch(arch, ev, priority, i) == self.act_no_match
                && (forall |j: int| self.included(j, priority, i)
                    ==> !#[trigger] self.rules@[j].group_matches(arch, self.archs@.contains(Arch::X32), ev))),
        decreases priority + 1, i
    {
        if priority >= 0 {
            if i == 0 {
                self.lemma_dispatch(arch, ev, priority - 1, self.rules@.len() as int);
            } else if self.rules@[i - 1].action.precedence() != priority
                || !self.rules@[i - 1].group_matches(arch, self.archs@.contains(Arch::X32), ev) {
                self.lemma_dispatch(arch, ev, priority, i - 1);
            }
        }
    }

    /// The policy accepts the action its blocks settle on.
    pub(super) proof fn lemma_blocks(self, ev: Event, i: int)
        requires
            self.wf(),
            0 <= i <= self.archs@.len(),
            forall |j: int| 0 <= j < i ==> !self.takes(#[trigger] self.archs@[j], ev),
        ensures self.eval(ev, self.blocks(ev, i))
        decreases self.archs@.len() - i
    {
        if i >= self.archs@.len() {
            assert forall |a: Arch| !self.is_active_arch(a, ev) by {
                if self.is_active_arch(a, ev) {
                    let arch = self.block_arch(a);
                    assert(self.archs@.contains(arch));
                    let j = choose |j: int| 0 <= j < self.archs@.len() && self.archs@[j] == arch;
                    assert(self.takes(self.archs@[j], ev));
                    assert(false);
                }
            }
        } else if self.takes(self.archs@[i], ev) {
            let arch = self.archs@[i];
            let act = self.dispatch(arch, ev, 8, self.rules@.len() as int);
            assert(self.archs@.contains(arch));
            Syscall::Skip.lemma_nr_ranges();
            let active = if arch == Arch::X86_64 && ev.nr == -1 && self.archs@.contains(Arch::X32) {
                Arch::X32
            } else { arch };
            assert(self.is_active_arch(active, ev));
            self.lemma_dispatch(arch, ev, 8, self.rules@.len() as int);
            assert forall |j: int| 0 <= j < self.rules@.len() implies
                self.included(j, 8, self.rules@.len() as int) by {
                assert(self.rules@[j].action.precedence() <= 8);
            }
            if exists |j: int| 0 <= j < self.rules@.len()
                && #[trigger] self.rules@[j].group_matches(arch, self.archs@.contains(Arch::X32), ev)
                && self.rules@[j].action == act {
                let j = choose |j: int| {
                    &&& self.included(j, 8, self.rules@.len() as int)
                    &&& #[trigger] self.rules@[j].group_matches(arch, self.archs@.contains(Arch::X32), ev)
                    &&& self.rules@[j].action == act
                    &&& forall |k: int| self.included(k, 8, self.rules@.len() as int)
                        && #[trigger] self.rules@[k].group_matches(arch, self.archs@.contains(Arch::X32), ev) ==> {
                            &&& self.rules@[k].action.precedence() <= self.rules@[j].action.precedence()
                            &&& self.rules@[k].action.precedence() == self.rules@[j].action.precedence() ==> k <= j
                        }
                };
                let a = if self.rules@[j].direct_enabled(arch, self.archs@.contains(Arch::X32))
                    && self.rules@[j].eval(arch, ev) { arch } else { Arch::X32 };
                self.rules@[j].syscall.lemma_nr_ranges();
                self.rules@[j].lemma_x32(ev);
                assert(self.is_active_arch(a, ev));
                assert(self.rules@[j].eval(a, ev));
                assert forall |k: int| #![trigger self.rules@[k]]
                    0 <= k < self.rules@.len() && k != j && self.rules@[k].eval(a, ev) implies {
                        ||| self.rules@[k].action.precedence() < act.precedence()
                        ||| k < j && self.rules@[k].action.precedence() == act.precedence()
                    } by {
                    self.rules@[k].syscall.lemma_nr_ranges();
                    assert(self.rules@[k].group_matches(arch, self.archs@.contains(Arch::X32), ev));
                    assert(self.included(k, 8, self.rules@.len() as int));
                }
                assert(self.eval(ev, act));
            } else {
                assert forall |a: Arch, j: int| self.is_active_arch(a, ev)
                    && 0 <= j < self.rules@.len()
                    implies !#[trigger] self.rules@[j].eval(a, ev) by {
                    self.rules@[j].syscall.lemma_nr_ranges();
                    assert(self.block_arch(a) == arch);
                    assert(!self.rules@[j].group_matches(arch, self.archs@.contains(Arch::X32), ev));
                }
                assert(self.eval(ev, act));
            }
        } else {
            self.lemma_blocks(ev, i + 1);
        }
    }

    /// Matching rules for one event use the same active architecture.
    pub(super) proof fn lemma_matching_arch_unique(self, ev: Event, a: Arch, b: Arch, i: int, j: int)
        requires
            self.is_active_arch(a, ev), self.is_active_arch(b, ev),
            0 <= i < self.rules@.len(), 0 <= j < self.rules@.len(),
            self.rules@[i].eval(a, ev), self.rules@[j].eval(b, ev),
        ensures a == b
    {
        if a != b {
            self.rules@[i].syscall.lemma_nr_ranges();
            self.rules@[j].syscall.lemma_nr_ranges();
            assert(a == Arch::X86_64 || a == Arch::X32);
            assert(b == Arch::X86_64 || b == Arch::X32);
            assert(ev.nr == -1);
            assert(false);
        }
    }

    /// Whether this rule is the ordered match selected for the event.
    pub(super) open spec fn wins(self, ev: Event, a: Arch, i: int) -> bool {
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
    pub(super) proof fn lemma_eval_witness(self, ev: Event, act: Action, a: Arch, i: int)
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

    /// An accepted action comes from a winning rule or an applicable fallback.
    pub(super) proof fn lemma_eval_cases(self, ev: Event, act: Action)
        requires self.wf(), self.eval(ev, act)
        ensures
            (exists |a: Arch, i: int| #[trigger] self.wins(ev, a, i) && self.rules@[i].action == act)
            || (act == self.act_bad_arch && forall |a: Arch| !self.is_active_arch(a, ev))
            || (act == self.act_no_match && exists |a: Arch| self.is_active_arch(a, ev)),
    {
        if exists |a: Arch, i: int| self.is_active_arch(a, ev)
            && 0 <= i < self.rules@.len() && #[trigger] self.rules@[i].eval(a, ev) {
            let (a, i) = choose |a: Arch, i: int| self.is_active_arch(a, ev)
                && 0 <= i < self.rules@.len() && #[trigger] self.rules@[i].eval(a, ev);
            self.lemma_eval_witness(ev, act, a, i);
        }
    }

    /// Two accepted actions for an event are equal.
    pub(super) proof fn lemma_eval_unique(self, ev: Event, act1: Action, act2: Action)
        requires self.wf(), self.eval(ev, act1), self.eval(ev, act2)
        ensures act1 == act2
    {
        self.lemma_eval_cases(ev, act1);
        self.lemma_eval_cases(ev, act2);
        if exists |a: Arch, i: int| #[trigger] self.wins(ev, a, i) && self.rules@[i].action == act1 {
            let (a, i) = choose |a: Arch, i: int| #[trigger] self.wins(ev, a, i) && self.rules@[i].action == act1;
            self.lemma_eval_witness(ev, act2, a, i);
            let (b, j) = choose |b: Arch, j: int| #[trigger] self.wins(ev, b, j) && self.rules@[j].action == act2;
            self.lemma_matching_arch_unique(ev, a, b, i, j);
            assert(i == j);
        } else if exists |b: Arch, j: int| #[trigger] self.wins(ev, b, j) && self.rules@[j].action == act2 {
            let (b, j) = choose |b: Arch, j: int| #[trigger] self.wins(ev, b, j) && self.rules@[j].action == act2;
            self.lemma_eval_witness(ev, act1, b, j);
            assert(false);
        }
    }
}

} // verus!
