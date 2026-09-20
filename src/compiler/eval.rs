//! What the filter computes, told as a policy-level account of its blocks and rule tests.

use vstd::prelude::*;
use crate::spec::policy::*;

verus! {

impl SyscallName {
    /// No syscall a multiplexer reaches answers to the multiplexer's own x86 number.
    pub(super) broadcast proof fn lemma_mux_nr(&self)
        ensures
            #[trigger] self.to_socketcall_arg() is Some
                ==> self.spec_nr(Arch::X86) != Self::Socketcall.spec_nr(Arch::X86),
            #[trigger] self.to_ipc_arg() is Some
                ==> self.spec_nr(Arch::X86) != Self::Ipc.spec_nr(Arch::X86),
    {
        reveal(SyscallName::spec_nr);
    }
}

impl Arch {
    /// Whether the x32 guard lets `ev` through, `has_x32` saying whether the policy covers
    /// x32 as well.
    pub(super) open spec fn admits(self, ev: Event, has_x32: bool) -> bool {
        &&& self == Arch::X86_64 ==> !ev.x32_bit() || (ev.is_skip() && !has_x32)
        &&& self == Arch::X32 ==> ev.x32_bit()
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
        ||| match self.syscall.spec_nr(arch) {
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
        broadcast use SyscallName::lemma_mux_nr;
        ev.lemma_nr();
        // The multiplexer's call number is the low word of the first argument.
        assert(forall |x: u64| #[trigger] (x & 0xFFFF_FFFF) < 0x1_0000_0000) by (bit_vector);
    }
}

impl Policy {
    /// Whether the block for `arch` takes `ev` on.
    pub(super) open spec fn takes(self, arch: Arch, ev: Event) -> bool {
        ev.matches_arch(arch) && arch.admits(ev, self.archs@.contains(Arch::X32))
    }

    /// The action the block for `arch` takes on `ev`, testing rules from `i` on.
    pub(super) open spec fn dispatch(self, arch: Arch, ev: Event, i: int) -> Action
        decreases self.rules@.len() - i
    {
        if i >= self.rules@.len() {
            self.attrs.act_default
        } else if self.rules@[i].eval(arch, ev) {
            self.rules@[i].action
        } else {
            self.dispatch(arch, ev, i + 1)
        }
    }

    /// The action the blocks for `archs[i..]` take on `ev`.
    pub(super) open spec fn blocks(self, ev: Event, i: int) -> Action
        decreases self.archs@.len() - i
    {
        if i >= self.archs@.len() {
            self.attrs.act_badarch
        } else if self.takes(self.archs@[i], ev) {
            self.dispatch(self.archs@[i], ev, 0)
        } else {
            self.blocks(ev, i + 1)
        }
    }

    /// The block for `arch` settles on the action of a rule it finds matching, or on the
    /// default action with no rule from `i` on matching.
    pub(super) proof fn lemma_dispatch(self, arch: Arch, ev: Event, i: int)
        requires 0 <= i <= self.rules@.len()
        ensures
            (exists |j: int| i <= j < self.rules@.len()
                && #[trigger] self.rules@[j].eval(arch, ev)
                && self.rules@[j].action == self.dispatch(arch, ev, i))
            || (self.dispatch(arch, ev, i) == self.attrs.act_default
                && (forall |j: int| i <= j < self.rules@.len()
                    ==> !#[trigger] self.rules@[j].eval(arch, ev))),
        decreases self.rules@.len() - i
    {
        if i < self.rules@.len() && !self.rules@[i].eval(arch, ev) {
            self.lemma_dispatch(arch, ev, i + 1);
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
            // No block claimed `ev`, so no architecture the policy covers is active on it.
            assert forall |a: Arch| !self.is_active_arch(a, ev) by {
                if self.is_active_arch(a, ev) {
                    let ja = choose |j: int| 0 <= j < self.archs@.len() && self.archs@[j] == a;
                    assert(!self.takes(self.archs@[ja], ev));
                    assert(false);
                }
            }
        } else if self.takes(self.archs@[i], ev) {
            let arch = self.archs@[i];
            let act = self.dispatch(arch, ev, 0);
            assert(self.archs@.contains(arch));
            assert(self.is_active_arch(arch, ev));
            self.lemma_dispatch(arch, ev, 0);
            if exists |j: int| 0 <= j < self.rules@.len()
                && #[trigger] self.rules@[j].eval(arch, ev)
                && self.rules@[j].action == self.dispatch(arch, ev, 0)
            {
                assert(self.eval(ev, act));
            } else {
                assert forall |a: Arch, j: int|
                    self.is_active_arch(a, ev) && 0 <= j < self.rules@.len()
                    implies !#[trigger] self.rules@[j].eval(a, ev) by
                {
                    assert(!self.rules@[j].eval(arch, ev));
                    if a != arch {
                        // Only x86_64 and x32 share an architecture token, and the guard that
                        // let `ev` into this block turns it away from the other of the pair.
                        assert(ev.matches_arch(a) && ev.matches_arch(arch));
                        assert(self.archs@.contains(a));
                        assert(false);
                    }
                }
                assert(self.eval(ev, act));
            }
        } else {
            self.lemma_blocks(ev, i + 1);
        }
    }
}

} // verus!
