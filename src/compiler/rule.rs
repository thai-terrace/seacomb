//! Compiling one rule: the test that reaches it, and the argument tests under it.

use vstd::prelude::*;
use crate::spec::{policy::*, syscall::*, cbpf::*};
use super::CompileError;
use super::builder::{Builder, Label};

verus! {

impl Arch {
    /// Executable version of [`Arch::mask`], which only ever says 32 or 64 bits.
    fn is_64bit(self) -> (res: bool)
        ensures res == (self.mask() == u64::MAX)
    {
        self == Arch::X86_64 || self == Arch::Aarch64
    }
}

impl Action {
    /// Executable version of [`Action::precedence`].
    pub(super) fn priority(&self) -> (res: u8)
        ensures res == self.precedence()
    {
        match self {
            Action::KillProcess => 7,
            Action::KillThread => 6,
            Action::Trap(_) => 5,
            Action::Errno(_) => 4,
            Action::Notify => 3,
            Action::Trace(_) => 2,
            Action::Log => 1,
            Action::Allow => 0,
        }
    }

    /// The filter return value that makes the kernel take this action.
    pub open spec fn spec_to_ret(&self) -> u32 {
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

    /// [`Action::spec_to_ret`] is the inverse of [`Action::from_ret`].
    pub broadcast proof fn lemma_to_ret(&self)
        ensures Action::from_ret(#[trigger] self.spec_to_ret()) == *self
    {
        let data = match self {
            Action::Trap(data) => *data,
            Action::Errno(data) => *data,
            Action::Trace(data) => *data,
            _ => 0,
        };
        let d = data as u32;
        assert(d < 0x1_0000);
        assert(0x0000_0000u32 & 0xffff_0000u32 == 0x0000_0000u32
            && 0x8000_0000u32 & 0xffff_0000u32 == 0x8000_0000u32
            && 0x7fc0_0000u32 & 0xffff_0000u32 == 0x7fc0_0000u32
            && 0x7ffc_0000u32 & 0xffff_0000u32 == 0x7ffc_0000u32
            && 0x7fff_0000u32 & 0xffff_0000u32 == 0x7fff_0000u32) by (bit_vector);
        assert((0x0003_0000u32 | d) & 0xffff_0000u32 == 0x0003_0000u32) by (bit_vector) requires d < 0x1_0000;
        assert((0x0005_0000u32 | d) & 0xffff_0000u32 == 0x0005_0000u32) by (bit_vector) requires d < 0x1_0000;
        assert((0x7ff0_0000u32 | d) & 0xffff_0000u32 == 0x7ff0_0000u32) by (bit_vector) requires d < 0x1_0000;
        assert((0x0003_0000u32 | d) & 0x0000_ffffu32 == d) by (bit_vector) requires d < 0x1_0000;
        assert((0x0005_0000u32 | d) & 0x0000_ffffu32 == d) by (bit_vector) requires d < 0x1_0000;
        assert((0x7ff0_0000u32 | d) & 0x0000_ffffu32 == d) by (bit_vector) requires d < 0x1_0000;
    }

    /// Executable version of [`Action::spec_to_ret`].
    #[verifier::when_used_as_spec(spec_to_ret)]
    pub(super) fn to_ret(&self) -> (res: u32)
        ensures res == self.spec_to_ret()
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

impl ArgCmp {
    /// A masked equality of 32-bit words is the one the values they widen to make.
    proof fn lemma_masked_words(x: u32, a: u32, b: u32)
        ensures ((x as u64) & (a as u64) == (b as u64) & (a as u64)) <==> (x & a == b & a)
    {
        assert(((x as u64) & (a as u64) == (b as u64) & (a as u64)) <==> (x & a == b & a))
            by (bit_vector);
    }

    /// What this test comes to on the word the filter loads for a 32-bit argument.
    proof fn lemma_words_32(self, arch: Arch, data: &[u8], xl: u32)
        requires
            self.arg < Rule::ARG_COUNT_MAX,
            Event::parse(data) is Some,
            arch.mask() == 0xFFFF_FFFF,
            xl == Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * self.arg) as u32),
        ensures
            self.op is Eq ==> (self.holds(arch, Event::of(data).args)
                <==> xl == self.a as u32),
            self.op is Ne ==> (self.holds(arch, Event::of(data).args)
                <==> xl != self.a as u32),
            self.op is Lt ==> (self.holds(arch, Event::of(data).args)
                <==> xl < self.a as u32),
            self.op is Le ==> (self.holds(arch, Event::of(data).args)
                <==> xl <= self.a as u32),
            self.op is Gt ==> (self.holds(arch, Event::of(data).args)
                <==> xl > self.a as u32),
            self.op is Ge ==> (self.holds(arch, Event::of(data).args)
                <==> xl >= self.a as u32),
            self.op is MaskedEq ==> (self.holds(arch, Event::of(data).args)
                <==> xl & (self.a as u32) == (self.b as u32) & (self.a as u32)),
    {
        let x = Event::of(data).args[self.arg as int];
        Event::lemma_image(data);
        assert(Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * self.arg) as u32)
            == (x & 0xFFFF_FFFF) as u32);
        ArgCmp::lemma_words(x, self.a);
        ArgCmp::lemma_words(self.a, x);
        ArgCmp::lemma_words(self.b, self.a);
        Self::lemma_masked_words(xl, self.a as u32, self.b as u32);
    }

    /// What this test comes to on the two words the filter loads for a 64-bit argument.
    proof fn lemma_words_64(self, arch: Arch, data: &[u8], xl: u32, xh: u32)
        requires
            self.arg < Rule::ARG_COUNT_MAX,
            Event::parse(data) is Some,
            arch.mask() == u64::MAX,
            xl == Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * self.arg) as u32),
            xh == Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * self.arg + 4) as u32),
        ensures
            self.op is Eq ==> (self.holds(arch, Event::of(data).args)
                <==> xh == (self.a >> 32) as u32 && xl == self.a as u32),
            self.op is Ne ==> (self.holds(arch, Event::of(data).args)
                <==> !(xh == (self.a >> 32) as u32 && xl == self.a as u32)),
            self.op is Lt ==> (self.holds(arch, Event::of(data).args)
                <==> xh < (self.a >> 32) as u32
                    || (xh == (self.a >> 32) as u32 && xl < self.a as u32)),
            self.op is Le ==> (self.holds(arch, Event::of(data).args)
                <==> xh < (self.a >> 32) as u32
                    || (xh == (self.a >> 32) as u32 && xl <= self.a as u32)),
            self.op is Gt ==> (self.holds(arch, Event::of(data).args)
                <==> xh > (self.a >> 32) as u32
                    || (xh == (self.a >> 32) as u32 && xl > self.a as u32)),
            self.op is Ge ==> (self.holds(arch, Event::of(data).args)
                <==> xh > (self.a >> 32) as u32
                    || (xh == (self.a >> 32) as u32 && xl >= self.a as u32)),
            self.op is MaskedEq ==> (self.holds(arch, Event::of(data).args)
                <==> xh & (self.a >> 32) as u32
                        == (self.b >> 32) as u32 & (self.a >> 32) as u32
                    && xl & (self.a as u32) == (self.b as u32) & (self.a as u32)),
    {
        let x = Event::of(data).args[self.arg as int];
        Event::lemma_image(data);
        assert(Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * self.arg) as u32)
            == (x & 0xFFFF_FFFF) as u32);
        assert(Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * self.arg + 4) as u32)
            == (x >> 32) as u32);
        ArgCmp::lemma_words(x, self.a);
        ArgCmp::lemma_words(self.a, x);
        ArgCmp::lemma_words(self.b, self.a);
        ArgCmp::lemma_words(x & self.a, self.b & self.a);
    }

    /// The load at the front of `ext` hands the word it reads to the code behind it.
    proof fn lemma_load(rev: Seq<Instr>, ext: Seq<Instr>, data: &[u8], k: u32, a: u32, to: nat)
        requires
            ext == rev.push(Instr::LdAbs(k)),
            k + 4 <= data@.len(),
            Builder::lands(rev, data, rev.len(), Builder::word(data, k), to),
        ensures Builder::lands(ext, data, ext.len(), a, to)
    {
        assert(Builder::extends(rev, ext));
        assert(ext[ext.len() - 1] == Instr::LdAbs(k));
        Builder::lemma_ld(ext, k);
        assert(Builder::goes_to(ext, data, ext.len(), a, rev.len(), Builder::word(data, k)));
        Builder::lemma_then(rev, ext, data, ext.len(), a, rev.len(),
            Builder::word(data, k), to, 0);
    }

    /// A landing behind `rev` is still one once the code in front of it has carried on there.
    proof fn lemma_step(rev: Seq<Instr>, ext: Seq<Instr>, data: &[u8], a: u32, mid: nat, m: u32, to: nat)
        requires
            Builder::extends(rev, ext),
            Builder::goes_to(ext, data, ext.len(), a, mid, m),
            Builder::lands(rev, data, mid, m, to),
        ensures Builder::lands(ext, data, ext.len(), a, to)
    {
        Builder::lemma_then(rev, ext, data, ext.len(), a, mid, m, to, 0);
    }

    /// The mask at the front of `ext` hands the masked word to the code behind it.
    proof fn lemma_mask(rev: Seq<Instr>, ext: Seq<Instr>, data: &[u8], k: u32, a: u32)
        requires ext == rev.push(Instr::Alu(AluOp::And, Src::K(k)))
        ensures Builder::goes_to(ext, data, ext.len(), a, rev.len(), a & k)
    {
        Builder::lemma_alu(ext, AluOp::And, k);
        assert(Builder::goes_to(ext, data, ext.len(), a, (ext.len() - 1) as nat,
            AluOp::And.eval(a, k)));
    }

    /// A test of the word loaded at the front of `s2` decides where entering `s3` lands.
    proof fn lemma_chain(s1: Seq<Instr>, s2: Seq<Instr>, s3: Seq<Instr>, data: &[u8],
        k: u32, xh: u32, to: nat)
        requires
            s2 == s1.push(Instr::LdAbs(k)),
            k + 4 <= data@.len(),
            Builder::extends(s2, s3),
            Builder::goes_to(s3, data, s3.len(), xh, s2.len(), xh),
            Builder::goes_to(s1, data, s1.len(), Builder::word(data, k), to,
                Builder::word(data, k)),
        ensures Builder::lands(s3, data, s3.len(), xh, to)
    {
        assert(Builder::lands(s1, data, s1.len(), Builder::word(data, k), to));
        Self::lemma_load(s1, s2, data, k, xh, to);
        Self::lemma_step(s2, s3, data, xh, s2.len(), xh, to);
    }

    /// A test of the masked word loaded at the front of `s3` decides where entering
    /// `s4` lands.
    proof fn lemma_chain_masked(s1: Seq<Instr>, s2: Seq<Instr>, s3: Seq<Instr>, s4: Seq<Instr>,
        data: &[u8], k: u32, m1: u32, m2: u32, to: nat)
        requires
            s3 == s2.push(Instr::LdAbs(k)),
            k + 4 <= data@.len(),
            Builder::extends(s1, s2),
            Builder::extends(s3, s4),
            Builder::goes_to(s1, data, s1.len(), m1, to, m1),
            Builder::goes_to(s2, data, s2.len(), Builder::word(data, k), s1.len(), m1),
            Builder::goes_to(s4, data, s4.len(), m2, s3.len(), m2),
        ensures Builder::lands(s4, data, s4.len(), m2, to)
    {
        assert(Builder::lands(s1, data, s1.len(), m1, to));
        Self::lemma_step(s1, s2, data, Builder::word(data, k), s1.len(), m1, to);
        Self::lemma_load(s2, s3, data, k, m2, to);
        Self::lemma_step(s3, s4, data, m2, s3.len(), m2, to);
    }

    /// The two-word equality test lands at `pass` when it holds and at `fail`
    /// when it does not.
    proof fn lemma_test_eq(self, arch: Arch, s1: Seq<Instr>, s2: Seq<Instr>, s3: Seq<Instr>,
        lo: u32, hi: u32, pass: nat, fail: nat)
        requires
            self.op is Eq,
            self.arg < Rule::ARG_COUNT_MAX,
            arch.mask() == u64::MAX,
            lo == (Policy::OFFSET_EVENT_ARGS + 8 * self.arg) as u32,
            hi == lo + 4,
            s2 == s1.push(Instr::LdAbs(lo)),
            Builder::extends(s2, s3),
            forall |data: &[u8], a: u32| a != self.a as u32 ==>
                #[trigger] Builder::goes_to(s1, data, s1.len(), a, fail, a),
            forall |data: &[u8], a: u32| a == self.a as u32 ==>
                #[trigger] Builder::goes_to(s1, data, s1.len(), a, pass, a),
            forall |data: &[u8], a: u32| a != (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s3, data, s3.len(), a, fail, a),
            forall |data: &[u8], a: u32| a == (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s3, data, s3.len(), a, s2.len(), a),
        ensures
            forall |data: &[u8]| Event::parse(data) is Some
                && self.holds(arch, Event::of(data).args) ==>
                #[trigger] Builder::lands(s3, data, s3.len(),
                    Builder::word(data, hi), pass),
            forall |data: &[u8]| Event::parse(data) is Some
                && !self.holds(arch, Event::of(data).args) ==>
                #[trigger] Builder::lands(s3, data, s3.len(),
                    Builder::word(data, hi), fail),
    {
        let a_hi = (self.a >> 32) as u32;
        assert forall |data: &[u8]| Event::parse(data) is Some
            && self.holds(arch, Event::of(data).args) implies
            #[trigger] Builder::lands(s3, data, s3.len(),
                Builder::word(data, hi), pass) by {
            let xl = Builder::word(data, lo);
            let xh = Builder::word(data, hi);
            self.lemma_words_64(arch, data, xl, xh);
            assert(Builder::goes_to(s1, data, s1.len(), xl, pass, xl));
            assert(Builder::goes_to(s3, data, s3.len(), xh, s2.len(), xh));
            Self::lemma_chain(s1, s2, s3, data, lo, xh, pass);
        }
        assert forall |data: &[u8]| Event::parse(data) is Some
            && !self.holds(arch, Event::of(data).args) implies
            #[trigger] Builder::lands(s3, data, s3.len(),
                Builder::word(data, hi), fail) by {
            let xl = Builder::word(data, lo);
            let xh = Builder::word(data, hi);
            self.lemma_words_64(arch, data, xl, xh);
            if xh == a_hi {
                assert(Builder::goes_to(s1, data, s1.len(), xl, fail, xl));
                assert(Builder::goes_to(s3, data, s3.len(), xh, s2.len(), xh));
                Self::lemma_chain(s1, s2, s3, data, lo, xh, fail);
            } else {
                assert(Builder::goes_to(s3, data, s3.len(), xh, fail, xh));
                assert(Builder::lands(s3, data, s3.len(), xh, fail));
            }
        }
    }

    /// The two-word inequality test lands at `pass` when it holds and at `fail`
    /// when it does not.
    proof fn lemma_test_ne(self, arch: Arch, s1: Seq<Instr>, s2: Seq<Instr>, s3: Seq<Instr>,
        lo: u32, hi: u32, pass: nat, fail: nat)
        requires
            self.op is Ne,
            self.arg < Rule::ARG_COUNT_MAX,
            arch.mask() == u64::MAX,
            lo == (Policy::OFFSET_EVENT_ARGS + 8 * self.arg) as u32,
            hi == lo + 4,
            s2 == s1.push(Instr::LdAbs(lo)),
            Builder::extends(s2, s3),
            forall |data: &[u8], a: u32| a == self.a as u32 ==>
                #[trigger] Builder::goes_to(s1, data, s1.len(), a, fail, a),
            forall |data: &[u8], a: u32| a != self.a as u32 ==>
                #[trigger] Builder::goes_to(s1, data, s1.len(), a, pass, a),
            forall |data: &[u8], a: u32| a != (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s3, data, s3.len(), a, pass, a),
            forall |data: &[u8], a: u32| a == (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s3, data, s3.len(), a, s2.len(), a),
        ensures
            forall |data: &[u8]| Event::parse(data) is Some
                && self.holds(arch, Event::of(data).args) ==>
                #[trigger] Builder::lands(s3, data, s3.len(),
                    Builder::word(data, hi), pass),
            forall |data: &[u8]| Event::parse(data) is Some
                && !self.holds(arch, Event::of(data).args) ==>
                #[trigger] Builder::lands(s3, data, s3.len(),
                    Builder::word(data, hi), fail),
    {
        let a_hi = (self.a >> 32) as u32;
        assert forall |data: &[u8]| Event::parse(data) is Some
            && self.holds(arch, Event::of(data).args) implies
            #[trigger] Builder::lands(s3, data, s3.len(),
                Builder::word(data, hi), pass) by {
            let xl = Builder::word(data, lo);
            let xh = Builder::word(data, hi);
            self.lemma_words_64(arch, data, xl, xh);
            if xh == a_hi {
                assert(Builder::goes_to(s1, data, s1.len(), xl, pass, xl));
                assert(Builder::goes_to(s3, data, s3.len(), xh, s2.len(), xh));
                Self::lemma_chain(s1, s2, s3, data, lo, xh, pass);
            } else {
                assert(Builder::goes_to(s3, data, s3.len(), xh, pass, xh));
                assert(Builder::lands(s3, data, s3.len(), xh, pass));
            }
        }
        assert forall |data: &[u8]| Event::parse(data) is Some
            && !self.holds(arch, Event::of(data).args) implies
            #[trigger] Builder::lands(s3, data, s3.len(),
                Builder::word(data, hi), fail) by {
            let xl = Builder::word(data, lo);
            let xh = Builder::word(data, hi);
            self.lemma_words_64(arch, data, xl, xh);
            assert(Builder::goes_to(s1, data, s1.len(), xl, fail, xl));
            assert(Builder::goes_to(s3, data, s3.len(), xh, s2.len(), xh));
            Self::lemma_chain(s1, s2, s3, data, lo, xh, fail);
        }
    }

    /// The two-word less-than test lands at `pass` when it holds and at `fail`
    /// when it does not.
    proof fn lemma_test_lt(self, arch: Arch, s1: Seq<Instr>, s2: Seq<Instr>, s3: Seq<Instr>, s4: Seq<Instr>,
        lo: u32, hi: u32, pass: nat, fail: nat)
        requires
            self.op is Lt,
            self.arg < Rule::ARG_COUNT_MAX,
            arch.mask() == u64::MAX,
            lo == (Policy::OFFSET_EVENT_ARGS + 8 * self.arg) as u32,
            hi == lo + 4,
            s2 == s1.push(Instr::LdAbs(lo)),
            Builder::extends(s2, s3),
            Builder::extends(s3, s4),
            forall |data: &[u8], a: u32| a >= self.a as u32 ==>
                #[trigger] Builder::goes_to(s1, data, s1.len(), a, fail, a),
            forall |data: &[u8], a: u32| a < self.a as u32 ==>
                #[trigger] Builder::goes_to(s1, data, s1.len(), a, pass, a),
            forall |data: &[u8], a: u32| a != (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s3, data, s3.len(), a, pass, a),
            forall |data: &[u8], a: u32| a == (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s3, data, s3.len(), a, s2.len(), a),
            forall |data: &[u8], a: u32| a > (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s4, data, s4.len(), a, fail, a),
            forall |data: &[u8], a: u32| a <= (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s4, data, s4.len(), a, s3.len(), a),
        ensures
            forall |data: &[u8]| Event::parse(data) is Some
                && self.holds(arch, Event::of(data).args) ==>
                #[trigger] Builder::lands(s4, data, s4.len(),
                    Builder::word(data, hi), pass),
            forall |data: &[u8]| Event::parse(data) is Some
                && !self.holds(arch, Event::of(data).args) ==>
                #[trigger] Builder::lands(s4, data, s4.len(),
                    Builder::word(data, hi), fail),
    {
        let a_hi = (self.a >> 32) as u32;
        assert forall |data: &[u8]| Event::parse(data) is Some
            && self.holds(arch, Event::of(data).args) implies
            #[trigger] Builder::lands(s4, data, s4.len(),
                Builder::word(data, hi), pass) by {
            let xl = Builder::word(data, lo);
            let xh = Builder::word(data, hi);
            self.lemma_words_64(arch, data, xl, xh);
            assert(Builder::goes_to(s4, data, s4.len(), xh, s3.len(), xh));
            if xh == a_hi {
                assert(Builder::goes_to(s1, data, s1.len(), xl, pass, xl));
                assert(Builder::goes_to(s3, data, s3.len(), xh, s2.len(), xh));
                Self::lemma_chain(s1, s2, s3, data, lo, xh, pass);
            } else {
                assert(Builder::goes_to(s3, data, s3.len(), xh, pass, xh));
                assert(Builder::lands(s3, data, s3.len(), xh, pass));
            }
            Self::lemma_step(s3, s4, data, xh, s3.len(), xh, pass);
        }
        assert forall |data: &[u8]| Event::parse(data) is Some
            && !self.holds(arch, Event::of(data).args) implies
            #[trigger] Builder::lands(s4, data, s4.len(),
                Builder::word(data, hi), fail) by {
            let xl = Builder::word(data, lo);
            let xh = Builder::word(data, hi);
            self.lemma_words_64(arch, data, xl, xh);
            if xh == a_hi {
                assert(Builder::goes_to(s1, data, s1.len(), xl, fail, xl));
                assert(Builder::goes_to(s3, data, s3.len(), xh, s2.len(), xh));
                Self::lemma_chain(s1, s2, s3, data, lo, xh, fail);
                assert(Builder::goes_to(s4, data, s4.len(), xh, s3.len(), xh));
                Self::lemma_step(s3, s4, data, xh, s3.len(), xh, fail);
            } else {
                assert(Builder::goes_to(s4, data, s4.len(), xh, fail, xh));
                assert(Builder::lands(s4, data, s4.len(), xh, fail));
            }
        }
    }

    /// The two-word less-or-equal test lands at `pass` when it holds and at `fail`
    /// when it does not.
    proof fn lemma_test_le(self, arch: Arch, s1: Seq<Instr>, s2: Seq<Instr>, s3: Seq<Instr>, s4: Seq<Instr>,
        lo: u32, hi: u32, pass: nat, fail: nat)
        requires
            self.op is Le,
            self.arg < Rule::ARG_COUNT_MAX,
            arch.mask() == u64::MAX,
            lo == (Policy::OFFSET_EVENT_ARGS + 8 * self.arg) as u32,
            hi == lo + 4,
            s2 == s1.push(Instr::LdAbs(lo)),
            Builder::extends(s2, s3),
            Builder::extends(s3, s4),
            forall |data: &[u8], a: u32| a > self.a as u32 ==>
                #[trigger] Builder::goes_to(s1, data, s1.len(), a, fail, a),
            forall |data: &[u8], a: u32| a <= self.a as u32 ==>
                #[trigger] Builder::goes_to(s1, data, s1.len(), a, pass, a),
            forall |data: &[u8], a: u32| a != (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s3, data, s3.len(), a, pass, a),
            forall |data: &[u8], a: u32| a == (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s3, data, s3.len(), a, s2.len(), a),
            forall |data: &[u8], a: u32| a > (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s4, data, s4.len(), a, fail, a),
            forall |data: &[u8], a: u32| a <= (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s4, data, s4.len(), a, s3.len(), a),
        ensures
            forall |data: &[u8]| Event::parse(data) is Some
                && self.holds(arch, Event::of(data).args) ==>
                #[trigger] Builder::lands(s4, data, s4.len(),
                    Builder::word(data, hi), pass),
            forall |data: &[u8]| Event::parse(data) is Some
                && !self.holds(arch, Event::of(data).args) ==>
                #[trigger] Builder::lands(s4, data, s4.len(),
                    Builder::word(data, hi), fail),
    {
        let a_hi = (self.a >> 32) as u32;
        assert forall |data: &[u8]| Event::parse(data) is Some
            && self.holds(arch, Event::of(data).args) implies
            #[trigger] Builder::lands(s4, data, s4.len(),
                Builder::word(data, hi), pass) by {
            let xl = Builder::word(data, lo);
            let xh = Builder::word(data, hi);
            self.lemma_words_64(arch, data, xl, xh);
            assert(Builder::goes_to(s4, data, s4.len(), xh, s3.len(), xh));
            if xh == a_hi {
                assert(Builder::goes_to(s1, data, s1.len(), xl, pass, xl));
                assert(Builder::goes_to(s3, data, s3.len(), xh, s2.len(), xh));
                Self::lemma_chain(s1, s2, s3, data, lo, xh, pass);
            } else {
                assert(Builder::goes_to(s3, data, s3.len(), xh, pass, xh));
                assert(Builder::lands(s3, data, s3.len(), xh, pass));
            }
            Self::lemma_step(s3, s4, data, xh, s3.len(), xh, pass);
        }
        assert forall |data: &[u8]| Event::parse(data) is Some
            && !self.holds(arch, Event::of(data).args) implies
            #[trigger] Builder::lands(s4, data, s4.len(),
                Builder::word(data, hi), fail) by {
            let xl = Builder::word(data, lo);
            let xh = Builder::word(data, hi);
            self.lemma_words_64(arch, data, xl, xh);
            if xh == a_hi {
                assert(Builder::goes_to(s1, data, s1.len(), xl, fail, xl));
                assert(Builder::goes_to(s3, data, s3.len(), xh, s2.len(), xh));
                Self::lemma_chain(s1, s2, s3, data, lo, xh, fail);
                assert(Builder::goes_to(s4, data, s4.len(), xh, s3.len(), xh));
                Self::lemma_step(s3, s4, data, xh, s3.len(), xh, fail);
            } else {
                assert(Builder::goes_to(s4, data, s4.len(), xh, fail, xh));
                assert(Builder::lands(s4, data, s4.len(), xh, fail));
            }
        }
    }

    /// The two-word greater-than test lands at `pass` when it holds and at `fail`
    /// when it does not.
    proof fn lemma_test_gt(self, arch: Arch, s1: Seq<Instr>, s2: Seq<Instr>, s3: Seq<Instr>, s4: Seq<Instr>,
        lo: u32, hi: u32, pass: nat, fail: nat)
        requires
            self.op is Gt,
            self.arg < Rule::ARG_COUNT_MAX,
            arch.mask() == u64::MAX,
            lo == (Policy::OFFSET_EVENT_ARGS + 8 * self.arg) as u32,
            hi == lo + 4,
            s2 == s1.push(Instr::LdAbs(lo)),
            Builder::extends(s2, s3),
            Builder::extends(s3, s4),
            forall |data: &[u8], a: u32| a <= self.a as u32 ==>
                #[trigger] Builder::goes_to(s1, data, s1.len(), a, fail, a),
            forall |data: &[u8], a: u32| a > self.a as u32 ==>
                #[trigger] Builder::goes_to(s1, data, s1.len(), a, pass, a),
            forall |data: &[u8], a: u32| a != (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s3, data, s3.len(), a, fail, a),
            forall |data: &[u8], a: u32| a == (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s3, data, s3.len(), a, s2.len(), a),
            forall |data: &[u8], a: u32| a > (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s4, data, s4.len(), a, pass, a),
            forall |data: &[u8], a: u32| a <= (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s4, data, s4.len(), a, s3.len(), a),
        ensures
            forall |data: &[u8]| Event::parse(data) is Some
                && self.holds(arch, Event::of(data).args) ==>
                #[trigger] Builder::lands(s4, data, s4.len(),
                    Builder::word(data, hi), pass),
            forall |data: &[u8]| Event::parse(data) is Some
                && !self.holds(arch, Event::of(data).args) ==>
                #[trigger] Builder::lands(s4, data, s4.len(),
                    Builder::word(data, hi), fail),
    {
        let a_hi = (self.a >> 32) as u32;
        assert forall |data: &[u8]| Event::parse(data) is Some
            && self.holds(arch, Event::of(data).args) implies
            #[trigger] Builder::lands(s4, data, s4.len(),
                Builder::word(data, hi), pass) by {
            let xl = Builder::word(data, lo);
            let xh = Builder::word(data, hi);
            self.lemma_words_64(arch, data, xl, xh);
            if xh == a_hi {
                assert(Builder::goes_to(s1, data, s1.len(), xl, pass, xl));
                assert(Builder::goes_to(s3, data, s3.len(), xh, s2.len(), xh));
                Self::lemma_chain(s1, s2, s3, data, lo, xh, pass);
                assert(Builder::goes_to(s4, data, s4.len(), xh, s3.len(), xh));
                Self::lemma_step(s3, s4, data, xh, s3.len(), xh, pass);
            } else {
                assert(Builder::goes_to(s4, data, s4.len(), xh, pass, xh));
                assert(Builder::lands(s4, data, s4.len(), xh, pass));
            }
        }
        assert forall |data: &[u8]| Event::parse(data) is Some
            && !self.holds(arch, Event::of(data).args) implies
            #[trigger] Builder::lands(s4, data, s4.len(),
                Builder::word(data, hi), fail) by {
            let xl = Builder::word(data, lo);
            let xh = Builder::word(data, hi);
            self.lemma_words_64(arch, data, xl, xh);
            assert(Builder::goes_to(s4, data, s4.len(), xh, s3.len(), xh));
            if xh == a_hi {
                assert(Builder::goes_to(s1, data, s1.len(), xl, fail, xl));
                assert(Builder::goes_to(s3, data, s3.len(), xh, s2.len(), xh));
                Self::lemma_chain(s1, s2, s3, data, lo, xh, fail);
            } else {
                assert(Builder::goes_to(s3, data, s3.len(), xh, fail, xh));
                assert(Builder::lands(s3, data, s3.len(), xh, fail));
            }
            Self::lemma_step(s3, s4, data, xh, s3.len(), xh, fail);
        }
    }

    /// The two-word greater-or-equal test lands at `pass` when it holds and at `fail`
    /// when it does not.
    proof fn lemma_test_ge(self, arch: Arch, s1: Seq<Instr>, s2: Seq<Instr>, s3: Seq<Instr>, s4: Seq<Instr>,
        lo: u32, hi: u32, pass: nat, fail: nat)
        requires
            self.op is Ge,
            self.arg < Rule::ARG_COUNT_MAX,
            arch.mask() == u64::MAX,
            lo == (Policy::OFFSET_EVENT_ARGS + 8 * self.arg) as u32,
            hi == lo + 4,
            s2 == s1.push(Instr::LdAbs(lo)),
            Builder::extends(s2, s3),
            Builder::extends(s3, s4),
            forall |data: &[u8], a: u32| a < self.a as u32 ==>
                #[trigger] Builder::goes_to(s1, data, s1.len(), a, fail, a),
            forall |data: &[u8], a: u32| a >= self.a as u32 ==>
                #[trigger] Builder::goes_to(s1, data, s1.len(), a, pass, a),
            forall |data: &[u8], a: u32| a != (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s3, data, s3.len(), a, fail, a),
            forall |data: &[u8], a: u32| a == (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s3, data, s3.len(), a, s2.len(), a),
            forall |data: &[u8], a: u32| a > (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s4, data, s4.len(), a, pass, a),
            forall |data: &[u8], a: u32| a <= (self.a >> 32) as u32 ==>
                #[trigger] Builder::goes_to(s4, data, s4.len(), a, s3.len(), a),
        ensures
            forall |data: &[u8]| Event::parse(data) is Some
                && self.holds(arch, Event::of(data).args) ==>
                #[trigger] Builder::lands(s4, data, s4.len(),
                    Builder::word(data, hi), pass),
            forall |data: &[u8]| Event::parse(data) is Some
                && !self.holds(arch, Event::of(data).args) ==>
                #[trigger] Builder::lands(s4, data, s4.len(),
                    Builder::word(data, hi), fail),
    {
        let a_hi = (self.a >> 32) as u32;
        assert forall |data: &[u8]| Event::parse(data) is Some
            && self.holds(arch, Event::of(data).args) implies
            #[trigger] Builder::lands(s4, data, s4.len(),
                Builder::word(data, hi), pass) by {
            let xl = Builder::word(data, lo);
            let xh = Builder::word(data, hi);
            self.lemma_words_64(arch, data, xl, xh);
            if xh == a_hi {
                assert(Builder::goes_to(s1, data, s1.len(), xl, pass, xl));
                assert(Builder::goes_to(s3, data, s3.len(), xh, s2.len(), xh));
                Self::lemma_chain(s1, s2, s3, data, lo, xh, pass);
                assert(Builder::goes_to(s4, data, s4.len(), xh, s3.len(), xh));
                Self::lemma_step(s3, s4, data, xh, s3.len(), xh, pass);
            } else {
                assert(Builder::goes_to(s4, data, s4.len(), xh, pass, xh));
                assert(Builder::lands(s4, data, s4.len(), xh, pass));
            }
        }
        assert forall |data: &[u8]| Event::parse(data) is Some
            && !self.holds(arch, Event::of(data).args) implies
            #[trigger] Builder::lands(s4, data, s4.len(),
                Builder::word(data, hi), fail) by {
            let xl = Builder::word(data, lo);
            let xh = Builder::word(data, hi);
            self.lemma_words_64(arch, data, xl, xh);
            assert(Builder::goes_to(s4, data, s4.len(), xh, s3.len(), xh));
            if xh == a_hi {
                assert(Builder::goes_to(s1, data, s1.len(), xl, fail, xl));
                assert(Builder::goes_to(s3, data, s3.len(), xh, s2.len(), xh));
                Self::lemma_chain(s1, s2, s3, data, lo, xh, fail);
            } else {
                assert(Builder::goes_to(s3, data, s3.len(), xh, fail, xh));
                assert(Builder::lands(s3, data, s3.len(), xh, fail));
            }
            Self::lemma_step(s3, s4, data, xh, s3.len(), xh, fail);
        }
    }

    /// The two-word masked equality lands at `pass` when it holds and at `fail`
    /// when it does not.
    proof fn lemma_test_maskedeq(self, arch: Arch, s1: Seq<Instr>, s2: Seq<Instr>,
        s3: Seq<Instr>, s4: Seq<Instr>, s5: Seq<Instr>,
        lo: u32, hi: u32, pass: nat, fail: nat)
        requires
            self.op is MaskedEq,
            self.arg < Rule::ARG_COUNT_MAX,
            arch.mask() == u64::MAX,
            lo == (Policy::OFFSET_EVENT_ARGS + 8 * self.arg) as u32,
            hi == lo + 4,
            s2 == s1.push(Instr::Alu(AluOp::And, Src::K(self.a as u32))),
            s3 == s2.push(Instr::LdAbs(lo)),
            s5 == s4.push(Instr::Alu(AluOp::And, Src::K((self.a >> 32) as u32))),
            Builder::extends(s3, s4),
            forall |data: &[u8], a: u32|
                a != (self.b as u32) & (self.a as u32) ==>
                #[trigger] Builder::goes_to(s1, data, s1.len(), a, fail, a),
            forall |data: &[u8], a: u32|
                a == (self.b as u32) & (self.a as u32) ==>
                #[trigger] Builder::goes_to(s1, data, s1.len(), a, pass, a),
            forall |data: &[u8], a: u32|
                a != ((self.b >> 32) as u32) & ((self.a >> 32) as u32) ==>
                #[trigger] Builder::goes_to(s4, data, s4.len(), a, fail, a),
            forall |data: &[u8], a: u32|
                a == ((self.b >> 32) as u32) & ((self.a >> 32) as u32) ==>
                #[trigger] Builder::goes_to(s4, data, s4.len(), a, s3.len(), a),
        ensures
            forall |data: &[u8]| Event::parse(data) is Some
                && self.holds(arch, Event::of(data).args) ==>
                #[trigger] Builder::lands(s5, data, s5.len(),
                    Builder::word(data, hi), pass),
            forall |data: &[u8]| Event::parse(data) is Some
                && !self.holds(arch, Event::of(data).args) ==>
                #[trigger] Builder::lands(s5, data, s5.len(),
                    Builder::word(data, hi), fail),
    {
        let a_lo = self.a as u32;
        let a_hi = (self.a >> 32) as u32;
        let b_lo = self.b as u32;
        let b_hi = (self.b >> 32) as u32;
        assert forall |data: &[u8]| Event::parse(data) is Some
            && self.holds(arch, Event::of(data).args) implies
            #[trigger] Builder::lands(s5, data, s5.len(),
                Builder::word(data, hi), pass) by {
            let xl = Builder::word(data, lo);
            let xh = Builder::word(data, hi);
            self.lemma_words_64(arch, data, xl, xh);
            assert(Builder::goes_to(s1, data, s1.len(), xl & a_lo,
                pass, xl & a_lo));
            Self::lemma_mask(s1, s2, data, a_lo, xl);
            assert(Builder::goes_to(s4, data, s4.len(), xh & a_hi,
                s3.len(), xh & a_hi));
            Self::lemma_chain_masked(s1, s2, s3, s4, data, lo, xl & a_lo,
                xh & a_hi, pass);
            Self::lemma_mask(s4, s5, data, a_hi, xh);
            Self::lemma_step(s4, s5, data, xh, s4.len(), xh & a_hi, pass);
        }
        assert forall |data: &[u8]| Event::parse(data) is Some
            && !self.holds(arch, Event::of(data).args) implies
            #[trigger] Builder::lands(s5, data, s5.len(),
                Builder::word(data, hi), fail) by {
            let xl = Builder::word(data, lo);
            let xh = Builder::word(data, hi);
            self.lemma_words_64(arch, data, xl, xh);
            Self::lemma_mask(s4, s5, data, a_hi, xh);
            if xh & a_hi == b_hi & a_hi {
                assert(Builder::goes_to(s1, data, s1.len(), xl & a_lo,
                    fail, xl & a_lo));
                Self::lemma_mask(s1, s2, data, a_lo, xl);
                assert(Builder::goes_to(s4, data, s4.len(), xh & a_hi,
                    s3.len(), xh & a_hi));
                Self::lemma_chain_masked(s1, s2, s3, s4, data, lo, xl & a_lo,
                    xh & a_hi, fail);
            } else {
                assert(Builder::goes_to(s4, data, s4.len(), xh & a_hi,
                    fail, xh & a_hi));
                assert(Builder::lands(s4, data, s4.len(), xh & a_hi, fail));
            }
            Self::lemma_step(s4, s5, data, xh, s4.len(), xh & a_hi, fail);
        }
    }

    /// Emits this test of one argument, jumping to `fail` when it does not hold and
    /// falling through when it does.
    ///
    /// A 64-bit architecture takes two words per argument, and cBPF compares one word
    /// at a time, so an ordering test there settles on the high word unless the two
    /// are equal.
    fn emit(&self, b: &mut Builder, arch: Arch, fail: Label) -> (res: Result<(), CompileError>)
        requires
            self.arg < Rule::ARG_COUNT_MAX,
            0 < fail <= b.rev@.len(),
            b.wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], a: u32| Event::parse(data) is Some
                && self.holds(arch, Event::of(data).args) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(),
                    a, old(b).rev@.len()),
            res is Ok ==> forall |data: &[u8], a: u32| Event::parse(data) is Some
                && !self.holds(arch, Event::of(data).args) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(),
                    a, fail as nat),
    {
        let pass = b.label();
        let lo = Policy::OFFSET_EVENT_ARGS + 8 * self.arg;
        let hi = lo + 4;
        let a_lo = self.a as u32;
        let a_hi = (self.a >> 32) as u32;
        let b_lo = self.b as u32;
        let b_hi = (self.b >> 32) as u32;

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
                    let ghost masked = b.rev@;
                    b.emit(Instr::Alu(AluOp::And, Src::K(a_lo)));
                    proof {
                        let rev = b.rev@;
                        assert forall |data: &[u8]| Event::parse(data) is Some
                            && self.holds(arch, Event::of(data).args) implies
                            #[trigger] Builder::lands(rev, data, rev.len(),
                                Builder::word(data, lo), pass as nat) by {
                            let xl = Builder::word(data, lo);
                            self.lemma_words_32(arch, data, xl);
                            Self::lemma_mask(masked, rev, data, a_lo, xl);
                            assert(Builder::goes_to(masked, data, masked.len(), xl & a_lo,
                                pass as nat, xl & a_lo));
                            assert(Builder::lands(masked, data, masked.len(), xl & a_lo,
                                pass as nat));
                            Self::lemma_step(masked, rev, data, xl, masked.len(), xl & a_lo,
                                pass as nat);
                        }
                        assert forall |data: &[u8]| Event::parse(data) is Some
                            && !self.holds(arch, Event::of(data).args) implies
                            #[trigger] Builder::lands(rev, data, rev.len(),
                                Builder::word(data, lo), fail as nat) by {
                            let xl = Builder::word(data, lo);
                            self.lemma_words_32(arch, data, xl);
                            Self::lemma_mask(masked, rev, data, a_lo, xl);
                            assert(Builder::goes_to(masked, data, masked.len(), xl & a_lo,
                                fail as nat, xl & a_lo));
                            assert(Builder::lands(masked, data, masked.len(), xl & a_lo,
                                fail as nat));
                            Self::lemma_step(masked, rev, data, xl, masked.len(), xl & a_lo,
                                fail as nat);
                        }
                    }
                }
            }
            proof {
                let rev = b.rev@;
                if !(self.op is MaskedEq) {
                    assert forall |data: &[u8]| Event::parse(data) is Some
                        && self.holds(arch, Event::of(data).args) implies
                        #[trigger] Builder::lands(rev, data, rev.len(),
                            Builder::word(data, lo), pass as nat) by {
                        let xl = Builder::word(data, lo);
                        self.lemma_words_32(arch, data, xl);
                        assert(Builder::goes_to(rev, data, rev.len(), xl, pass as nat, xl));
                    }
                    assert forall |data: &[u8]| Event::parse(data) is Some
                        && !self.holds(arch, Event::of(data).args) implies
                        #[trigger] Builder::lands(rev, data, rev.len(),
                            Builder::word(data, lo), fail as nat) by {
                        let xl = Builder::word(data, lo);
                        self.lemma_words_32(arch, data, xl);
                        assert(Builder::goes_to(rev, data, rev.len(), xl, fail as nat, xl));
                    }
                }
                let ext = rev.push(Instr::LdAbs(lo));
                assert forall |data: &[u8], a: u32| Event::parse(data) is Some
                    && self.holds(arch, Event::of(data).args) implies
                    #[trigger] Builder::lands(ext, data, ext.len(), a, pass as nat) by {
                    Self::lemma_load(rev, ext, data, lo, a, pass as nat);
                }
                assert forall |data: &[u8], a: u32| Event::parse(data) is Some
                    && !self.holds(arch, Event::of(data).args) implies
                    #[trigger] Builder::lands(ext, data, ext.len(), a, fail as nat) by {
                    Self::lemma_load(rev, ext, data, lo, a, fail as nat);
                }
            }
            b.emit(Instr::LdAbs(lo));
            return Ok(());
        }

        match self.op {
            Compare::Eq => {
                b.emit_jump(JmpOp::Eq, Src::K(a_lo), false, fail)?;
                let ghost s1 = b.rev@;
                b.emit(Instr::LdAbs(lo));
                let ghost s2 = b.rev@;
                b.emit_jump(JmpOp::Eq, Src::K(a_hi), false, fail)?;
                proof {
                    self.lemma_test_eq(arch, s1, s2, b.rev@, lo, hi, pass as nat, fail as nat);
                }
            }
            Compare::Ne => {
                b.emit_jump(JmpOp::Eq, Src::K(a_lo), true, fail)?;
                let ghost s1 = b.rev@;
                b.emit(Instr::LdAbs(lo));
                let ghost s2 = b.rev@;
                b.emit_jump(JmpOp::Eq, Src::K(a_hi), false, pass)?;
                proof {
                    self.lemma_test_ne(arch, s1, s2, b.rev@, lo, hi, pass as nat, fail as nat);
                }
            }
            Compare::Lt => {
                b.emit_jump(JmpOp::Ge, Src::K(a_lo), true, fail)?;
                let ghost s1 = b.rev@;
                b.emit(Instr::LdAbs(lo));
                let ghost s2 = b.rev@;
                b.emit_jump(JmpOp::Eq, Src::K(a_hi), false, pass)?;
                let ghost s3 = b.rev@;
                b.emit_jump(JmpOp::Gt, Src::K(a_hi), true, fail)?;
                proof {
                    self.lemma_test_lt(arch, s1, s2, s3, b.rev@, lo, hi, pass as nat, fail as nat);
                }
            }
            Compare::Le => {
                b.emit_jump(JmpOp::Gt, Src::K(a_lo), true, fail)?;
                let ghost s1 = b.rev@;
                b.emit(Instr::LdAbs(lo));
                let ghost s2 = b.rev@;
                b.emit_jump(JmpOp::Eq, Src::K(a_hi), false, pass)?;
                let ghost s3 = b.rev@;
                b.emit_jump(JmpOp::Gt, Src::K(a_hi), true, fail)?;
                proof {
                    self.lemma_test_le(arch, s1, s2, s3, b.rev@, lo, hi, pass as nat, fail as nat);
                }
            }
            Compare::Gt => {
                b.emit_jump(JmpOp::Gt, Src::K(a_lo), false, fail)?;
                let ghost s1 = b.rev@;
                b.emit(Instr::LdAbs(lo));
                let ghost s2 = b.rev@;
                b.emit_jump(JmpOp::Eq, Src::K(a_hi), false, fail)?;
                let ghost s3 = b.rev@;
                b.emit_jump(JmpOp::Gt, Src::K(a_hi), true, pass)?;
                proof {
                    self.lemma_test_gt(arch, s1, s2, s3, b.rev@, lo, hi, pass as nat, fail as nat);
                }
            }
            Compare::Ge => {
                b.emit_jump(JmpOp::Ge, Src::K(a_lo), false, fail)?;
                let ghost s1 = b.rev@;
                b.emit(Instr::LdAbs(lo));
                let ghost s2 = b.rev@;
                b.emit_jump(JmpOp::Eq, Src::K(a_hi), false, fail)?;
                let ghost s3 = b.rev@;
                b.emit_jump(JmpOp::Gt, Src::K(a_hi), true, pass)?;
                proof {
                    self.lemma_test_ge(arch, s1, s2, s3, b.rev@, lo, hi, pass as nat, fail as nat);
                }
            }
            Compare::MaskedEq => {
                b.emit_jump(JmpOp::Eq, Src::K(b_lo & a_lo), false, fail)?;
                let ghost s1 = b.rev@;
                b.emit(Instr::Alu(AluOp::And, Src::K(a_lo)));
                let ghost s2 = b.rev@;
                b.emit(Instr::LdAbs(lo));
                let ghost s3 = b.rev@;
                b.emit_jump(JmpOp::Eq, Src::K(b_hi & a_hi), false, fail)?;
                let ghost s4 = b.rev@;
                b.emit(Instr::Alu(AluOp::And, Src::K(a_hi)));
                proof {
                    self.lemma_test_maskedeq(arch, s1, s2, s3, s4, b.rev@, lo, hi,
                        pass as nat, fail as nat);
                }
            }
        }
        proof {
            let rev = b.rev@;
            let ext = rev.push(Instr::LdAbs(hi));
            assert forall |data: &[u8], a: u32| Event::parse(data) is Some
                && self.holds(arch, Event::of(data).args) implies
                #[trigger] Builder::lands(ext, data, ext.len(), a, pass as nat) by {
                Self::lemma_load(rev, ext, data, hi, a, pass as nat);
            }
            assert forall |data: &[u8], a: u32| Event::parse(data) is Some
                && !self.holds(arch, Event::of(data).args) implies
                #[trigger] Builder::lands(ext, data, ext.len(), a, fail as nat) by {
                Self::lemma_load(rev, ext, data, hi, a, fail as nat);
            }
        }
        b.emit(Instr::LdAbs(hi));
        Ok(())
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
    fn emit(&self, b: &mut Builder, arch: Arch, nr: u32) -> (res: Result<(), CompileError>)
        requires
            forall |i: int| #![trigger self.conds@[i]]
                0 <= i < self.conds@.len() ==> self.conds@[i].arg < Self::ARG_COUNT_MAX,
            0 < b.rev@.len(),
            b.wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8]| Event::parse(data) is Some
                && self.matches_at(arch, nr, Event::of(data)) ==>
                #[trigger] Builder::returns(final(b).rev@, data, final(b).rev@.len(),
                    Event::of(data).nr as u32, self.action.to_ret()),
            res is Ok ==> forall |data: &[u8]| Event::parse(data) is Some
                && !self.matches_at(arch, nr, Event::of(data)) ==>
                #[trigger] Builder::goes_to(final(b).rev@, data, final(b).rev@.len(),
                    Event::of(data).nr as u32, old(b).rev@.len(), Event::of(data).nr as u32),
    {
        let end = b.label();
        b.emit(Instr::LdAbs(Policy::OFFSET_EVENT_NR));
        proof { Builder::lemma_ld(b.rev@, Policy::OFFSET_EVENT_NR); }
        let ghost r_nr = b.rev@;
        self.emit_body(b, arch, nr)?;
        let ghost r_body = b.rev@;
        b.emit_jump(JmpOp::Eq, Src::K(nr), false, end)?;
        proof {
            assert forall |data: &[u8]|
                #![trigger Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32, self.action.to_ret())]
                #![trigger Builder::goes_to(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                    end as nat, Event::of(data).nr as u32)]
                Event::parse(data) is Some implies
                if self.matches_at(arch, nr, Event::of(data)) {
                    Builder::returns(b.rev@, data, b.rev@.len(),
                        Event::of(data).nr as u32, self.action.to_ret())
                } else {
                    Builder::goes_to(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                        end as nat, Event::of(data).nr as u32)
                } by {
                let ev = Event::of(data);
                Event::lemma_image(data);
                if ev.nr as u32 == nr {
                    assert(Builder::goes_to(b.rev@, data, b.rev@.len(), nr, r_body.len(), nr));
                    if self.body_holds(arch, nr, ev) {
                        assert(Builder::returns(r_body, data, r_body.len(), nr, self.action.to_ret()));
                        Builder::lemma_then(r_body, b.rev@, data, b.rev@.len(), nr, r_body.len(), nr,
                            0, self.action.to_ret());
                    } else {
                        assert(Builder::lands(r_body, data, r_body.len(), nr, r_nr.len()));
                        assert(Builder::goes_to_all(r_nr, data, r_nr.len(), end as nat, nr));
                        Builder::lemma_then_any(r_nr, r_body, data, r_body.len(), nr, r_nr.len(),
                            end as nat, nr);
                        Builder::lemma_then(r_body, b.rev@, data, b.rev@.len(), nr, r_body.len(), nr,
                            end as nat, nr);
                    }
                }
            }
        }
        Ok(())
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
    fn emit_body(&self, b: &mut Builder, arch: Arch, nr: u32) -> (res: Result<(), CompileError>)
        requires
            forall |i: int| #![trigger self.conds@[i]]
                0 <= i < self.conds@.len() ==> self.conds@[i].arg < Self::ARG_COUNT_MAX,
            0 < b.rev@.len(),
            b.wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], a: u32| Event::parse(data) is Some
                && self.body_holds(arch, nr, Event::of(data)) ==>
                #[trigger] Builder::returns(final(b).rev@, data, final(b).rev@.len(),
                    a, self.action.to_ret()),
            res is Ok ==> forall |data: &[u8], a: u32| Event::parse(data) is Some
                && !self.body_holds(arch, nr, Event::of(data)) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(),
                    a, old(b).rev@.len()),
    {
        let end = b.label();
        let ghost base = b.rev@;
        b.emit(Instr::Ret(RetVal::K(self.action.to_ret())));
        let ghost r_ret = b.rev@;
        proof {
            Builder::lemma_ret(r_ret, self.action.to_ret());
            assert forall |data: &[u8], a: u32| #[trigger] Builder::returns(r_ret, data,
                r_ret.len(), a, self.action.to_ret()) by {
                assert(Builder::returns_all(r_ret, data, r_ret.len(), self.action.to_ret()));
            }
        }

        if let Some(arg) = self.mux_arg(arch) {
            if self.mux_nr(arch) == Some(nr) {
                b.emit_jump(JmpOp::Eq, Src::K(arg), false, end)?;
                let ghost r_sel = b.rev@;
                let ghost r_arg = r_sel.push(Instr::LdAbs(Policy::OFFSET_EVENT_ARGS));
                proof {
                    Builder::lemma_ld(r_arg, Policy::OFFSET_EVENT_ARGS);
                    assert forall |data: &[u8], a: u32|
                        Event::parse(data) is Some
                        && self.body_holds(arch, nr, Event::of(data))
                        implies #[trigger] Builder::returns(r_arg, data, r_arg.len(), a,
                            self.action.to_ret()) by {
                        Event::lemma_image(data);
                        assert(Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * 0) as u32)
                            == (Event::of(data).args[0] & 0xFFFF_FFFF) as u32);
                        let w = Builder::word(data, Policy::OFFSET_EVENT_ARGS);
                        assert(w == arg);
                        assert(Builder::goes_to_all(r_arg, data, r_arg.len(),
                            (r_arg.len() - 1) as nat, w));
                        assert(Builder::goes_to(r_arg, data, r_arg.len(), a, r_sel.len(), w));
                        assert(Builder::goes_to(r_sel, data, r_sel.len(), w, r_ret.len(), w));
                        Builder::lemma_then(r_ret, r_sel, data, r_sel.len(), w, r_ret.len(), w,
                            0, self.action.to_ret());
                        Builder::lemma_then(r_sel, r_arg, data, r_arg.len(), a, r_sel.len(), w,
                            0, self.action.to_ret());
                    }
                    assert forall |data: &[u8], a: u32|
                        Event::parse(data) is Some
                        && !self.body_holds(arch, nr, Event::of(data))
                        implies #[trigger] Builder::lands(r_arg, data, r_arg.len(), a,
                            base.len()) by {
                        Event::lemma_image(data);
                        assert(Builder::word(data, (Policy::OFFSET_EVENT_ARGS + 8 * 0) as u32)
                            == (Event::of(data).args[0] & 0xFFFF_FFFF) as u32);
                        let w = Builder::word(data, Policy::OFFSET_EVENT_ARGS);
                        assert(w != arg);
                        assert(Builder::goes_to_all(r_arg, data, r_arg.len(),
                            (r_arg.len() - 1) as nat, w));
                        assert(Builder::goes_to(r_arg, data, r_arg.len(), a, r_sel.len(), w));
                        assert(Builder::goes_to(r_sel, data, r_sel.len(), w, end as nat, w));
                        assert(Builder::lands(r_sel, data, r_sel.len(), w, end as nat));
                        Builder::lemma_then(r_sel, r_arg, data, r_arg.len(), a, r_sel.len(), w,
                            end as nat, w);
                    }
                }
                b.emit(Instr::LdAbs(Policy::OFFSET_EVENT_ARGS));
                return Ok(());
            }
        }

        let mut i = self.conds.len();
        while i > 0
            invariant
                i <= self.conds@.len(),
                forall |j: int| #![trigger self.conds@[j]]
                    0 <= j < self.conds@.len() ==> self.conds@[j].arg < Self::ARG_COUNT_MAX,
                0 < end == old(b).rev@.len(),
                b.wf(),
                Builder::extends(old(b).rev@, b.rev@),
                forall |data: &[u8], a: u32| Event::parse(data) is Some
                    && self.conds_hold(arch, Event::of(data), i as int) ==>
                    #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), a, self.action.to_ret()),
                forall |data: &[u8], a: u32| Event::parse(data) is Some
                    && !self.conds_hold(arch, Event::of(data), i as int) ==>
                    #[trigger] Builder::lands(b.rev@, data, b.rev@.len(), a, end as nat),
            decreases i
        {
            let ghost r_prev = b.rev@;
            i -= 1;
            self.conds[i].emit(b, arch, end)?;
            let ghost r_cond = b.rev@;
            proof {
                assert forall |data: &[u8], a: u32|
                    Event::parse(data) is Some
                    && self.conds_hold(arch, Event::of(data), i as int)
                    implies #[trigger] Builder::returns(r_cond, data, r_cond.len(), a,
                        self.action.to_ret()) by {
                    let ev = Event::of(data);
                    assert(self.conds@[i as int].holds(arch, ev.args));
                    assert(self.conds_hold(arch, ev, i + 1));
                    assert(Builder::lands(r_cond, data, r_cond.len(), a, r_prev.len()));
                    assert(Builder::returns_all(r_prev, data, r_prev.len(), self.action.to_ret()));
                    Builder::lemma_then_any(r_prev, r_cond, data, r_cond.len(), a, r_prev.len(),
                        0, self.action.to_ret());
                }
                assert forall |data: &[u8], a: u32|
                    Event::parse(data) is Some
                    && !self.conds_hold(arch, Event::of(data), i as int)
                    implies #[trigger] Builder::lands(r_cond, data, r_cond.len(), a,
                        end as nat) by {
                    let ev = Event::of(data);
                    if self.conds@[i as int].holds(arch, ev.args) {
                        assert(!self.conds_hold(arch, ev, i + 1));
                        assert(Builder::lands(r_cond, data, r_cond.len(), a, r_prev.len()));
                        let m = choose |m: u32| Builder::goes_to(r_cond, data, r_cond.len(), a,
                            r_prev.len(), m);
                        assert(Builder::lands(r_prev, data, r_prev.len(), m, end as nat));
                        Builder::lemma_then(r_prev, r_cond, data, r_cond.len(), a, r_prev.len(),
                            m, end as nat, a);
                    }
                }
            }
        }
        Ok(())
    }

    /// The call number the x86 multiplexer selects this rule's syscall on, if one
    /// reaches it.
    pub(super) open spec fn spec_mux_arg(&self, arch: Arch) -> Option<u32> {
        if arch != Arch::X86 || self.conds@.len() > 0 {
            None
        } else {
            match self.syscall.to_socketcall_arg() {
                Some(arg) => Some(arg as u32),
                None => match self.syscall.to_ipc_arg() {
                    Some(arg) => Some(arg as u32),
                    None => None,
                },
            }
        }
    }

    /// Executable version of [`Rule::spec_mux_arg`].
    #[verifier::when_used_as_spec(spec_mux_arg)]
    fn mux_arg(&self, arch: Arch) -> (res: Option<u32>)
        ensures res == self.spec_mux_arg(arch)
    {
        if arch != Arch::X86 || self.conds.len() > 0 {
            return None;
        }
        match self.syscall.socketcall_arg() {
            Some(arg) => Some(arg as u32),
            None => match self.syscall.ipc_arg() {
                Some(arg) => Some(arg as u32),
                None => None,
            },
        }
    }

    /// The number of the x86 multiplexer that also reaches this rule, if one does.
    pub(super) open spec fn spec_mux_nr(&self, arch: Arch) -> Option<u32> {
        if arch != Arch::X86 || self.conds@.len() > 0 {
            None
        } else {
            let mux = if self.syscall.to_socketcall_arg() is Some {
                Some(Syscall::Socketcall)
            } else if self.syscall.to_ipc_arg() is Some {
                Some(Syscall::Ipc)
            } else {
                None
            };
            match mux {
                Some(name) => match name.spec_nr(arch) {
                    Some(nr) => Some(nr as u32),
                    None => None,
                },
                None => None,
            }
        }
    }

    /// Executable version of [`Rule::spec_mux_nr`].
    #[verifier::when_used_as_spec(spec_mux_nr)]
    pub(super) fn mux_nr(&self, arch: Arch) -> (res: Option<u32>)
        ensures res == self.spec_mux_nr(arch)
    {
        // `Rule::eval` takes a multiplexed match only for a rule that tests no argument.
        if arch != Arch::X86 || self.conds.len() > 0 {
            return None;
        }
        let mux = if self.syscall.socketcall_arg().is_some() {
            Some(Syscall::Socketcall)
        } else if self.syscall.ipc_arg().is_some() {
            Some(Syscall::Ipc)
        } else {
            None
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

impl Rule {
    /// Emits the direct and multiplexed syscall tests for this rule.
    ///
    /// ```text
    ///     <direct syscall test and argument conditions>
    ///     <multiplexer test and call-number condition>
    /// ```
    pub(super) fn emit_tests(&self, b: &mut Builder, arch: Arch) -> (res: Result<(), CompileError>)
        requires
            forall |i: int| #![trigger self.conds@[i]]
                0 <= i < self.conds@.len() ==> self.conds@[i].arg < Self::ARG_COUNT_MAX,
            0 < b.rev@.len(), b.wf(),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8]| Event::parse(data) is Some
                && self.eval(arch, Event::of(data)) ==>
                #[trigger] Builder::returns(final(b).rev@, data, final(b).rev@.len(),
                    Event::of(data).nr as u32, self.action.to_ret()),
            res is Ok ==> forall |data: &[u8]| Event::parse(data) is Some
                && !self.eval(arch, Event::of(data)) ==>
                #[trigger] Builder::goes_to(final(b).rev@, data, final(b).rev@.len(),
                    Event::of(data).nr as u32, old(b).rev@.len(), Event::of(data).nr as u32),
    {
        let ghost prev = b.rev@;
        if let Some(nr) = self.mux_nr(arch) {
            self.emit(b, arch, nr)?;
        }
        let ghost mux = b.rev@;
        if let Some(nr) = self.syscall.bpf_nr(arch) {
            self.emit(b, arch, nr)?;
        }
        proof {
            assert forall |data: &[u8]|
                #![trigger Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32, self.action.to_ret())]
                #![trigger Builder::goes_to(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                    prev.len(), Event::of(data).nr as u32)]
                Event::parse(data) is Some implies
                if self.eval(arch, Event::of(data)) {
                    Builder::returns(b.rev@, data, b.rev@.len(),
                        Event::of(data).nr as u32, self.action.to_ret())
                } else {
                    Builder::goes_to(b.rev@, data, b.rev@.len(),
                        Event::of(data).nr as u32, prev.len(), Event::of(data).nr as u32)
                } by {
                let ev = Event::of(data);
                let nr = ev.nr as u32;
                Event::lemma_image(data);
                self.lemma_matches(arch, ev);
                let own = match self.syscall.spec_bpf_nr(arch) {
                    Some(n) => self.matches_at(arch, n, ev),
                    None => false,
                };
                if !own {
                    assert(Builder::goes_to(b.rev@, data, b.rev@.len(), nr, mux.len(), nr));
                    if self.eval(arch, ev) {
                        assert(Builder::returns(mux, data, mux.len(), nr, self.action.to_ret()));
                        Builder::lemma_then(mux, b.rev@, data, b.rev@.len(), nr, mux.len(), nr,
                            0, self.action.to_ret());
                    } else {
                        assert(Builder::goes_to(mux, data, mux.len(), nr, prev.len(), nr));
                        Builder::lemma_then(mux, b.rev@, data, b.rev@.len(), nr, mux.len(), nr,
                            prev.len(), nr);
                    }
                }
            }
        }
        Ok(())
    }
}

} // verus!
