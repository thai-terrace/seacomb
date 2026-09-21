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
        self == Arch::X32 ==> ev.x32_bit()
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

    /// Whether the rule matches either ABI served by this architecture block.
    pub(super) open spec fn group_matches(self, arch: Arch, has_x32: bool, ev: Event) -> bool {
        self.eval(arch, ev)
            || (arch == Arch::X86_64 && has_x32 && self.eval(Arch::X32, ev))
    }

    /// A matching x32 rule passes the architecture's syscall-number guard.
    pub(super) proof fn lemma_x32(self, ev: Event)
        ensures self.eval(Arch::X32, ev) ==> ev.x32_bit()
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
            self.attrs.act_default
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
            self.attrs.act_badarch
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
            }) || (self.dispatch(arch, ev, priority, i) == self.attrs.act_default
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
            assert(self.is_active_arch(arch, ev));
            self.lemma_dispatch(arch, ev, 8, self.rules@.len() as int);
            assert forall |j: int| 0 <= j < self.rules@.len() implies
                self.included(j, 8, self.rules@.len() as int) by {
                assert(self.rules@[j].action.precedence() <= 8);
            }
            if exists |j: int| 0 <= j < self.rules@.len()
                && #[trigger] self.rules@[j].group_matches(arch, self.archs@.contains(Arch::X32), ev)
                && self.rules@[j].action == act {
                let j = choose |j: int| 0 <= j < self.rules@.len()
                    && #[trigger] self.rules@[j].group_matches(arch, self.archs@.contains(Arch::X32), ev)
                    && self.rules@[j].action == act;
                let a = if self.rules@[j].eval(arch, ev) { arch } else { Arch::X32 };
                self.rules@[j].lemma_x32(ev);
                assert(self.is_active_arch(a, ev));
                assert(self.rules@[j].eval(a, ev));
                assert(self.eval(ev, act));
            } else {
                assert forall |a: Arch, j: int| self.is_active_arch(a, ev)
                    && 0 <= j < self.rules@.len()
                    implies !#[trigger] self.rules@[j].eval(a, ev) by {
                    assert(self.block_arch(a) == arch);
                    assert(!self.rules@[j].group_matches(arch, self.archs@.contains(Arch::X32), ev));
                }
                assert(self.eval(ev, act));
            }
        } else {
            self.lemma_blocks(ev, i + 1);
        }
    }
}

} // verus!
