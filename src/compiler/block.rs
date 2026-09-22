//! Compiling one architecture's block: the guard that claims an event, and the dispatch
//! of the policy's rules under it.

use vstd::prelude::*;
use crate::spec::{policy::*, cbpf::*};
use super::CompileError;
use super::builder::{Builder, Label};

verus! {

impl Arch {
    /// `AUDIT_ARCH_*` in `linux/audit.h`: what the kernel reports in
    /// `seccomp_data.arch`.
    pub const TOKEN_X86: u32 = 0x4000_0003;
    pub const TOKEN_X86_64: u32 = 0xC000_003E;
    pub const TOKEN_ARM: u32 = 0x4000_0028;
    pub const TOKEN_AARCH64: u32 = 0xC000_00B7;

    /// Executable version of [`Arch::token`].
    pub fn to_token(self) -> (res: u32)
        ensures res == self.token()
    {
        match self {
            Arch::X86 => Self::TOKEN_X86,
            Arch::X86_64 => Self::TOKEN_X86_64,
            Arch::Arm => Self::TOKEN_ARM,
            Arch::Aarch64 => Self::TOKEN_AARCH64,
        }
    }

    /// Emits the architecture guard and loads the syscall number on a match.
    ///
    /// ```text
    ///     ld  [arch]
    ///     jne #token -> end
    ///     ld  [nr]
    /// ```
    fn emit_guard(self, b: &mut Builder, end: Label) -> (res: Result<(), CompileError>)
        requires 0 < end <= b.rev@.len(), b.wf()
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8]| Event::parse(data) is Some
                && Event::of(data).arch == self.token() ==>
                #[trigger] Builder::goes_to_all(final(b).rev@, data, final(b).rev@.len(),
                    old(b).rev@.len(), Event::of(data).nr as u32),
            res is Ok ==> forall |data: &[u8]| Event::parse(data) is Some
                && Event::of(data).arch != self.token() ==>
                #[trigger] Builder::goes_to_all(final(b).rev@, data, final(b).rev@.len(),
                    end as nat, Event::of(data).arch),
    {
        let ghost body = b.rev@;
        b.emit(Instr::LdAbs(Policy::OFFSET_EVENT_NR));
        proof { Builder::lemma_ld(b.rev@, Policy::OFFSET_EVENT_NR); }
        let ghost loaded_nr = b.rev@;
        b.emit_jump(JmpOp::Eq, Src::K(self.to_token()), false, end)?;
        let ghost guarded_arch = b.rev@;
        b.emit(Instr::LdAbs(Policy::OFFSET_EVENT_ARCH));
        proof {
            Builder::lemma_ld(b.rev@, Policy::OFFSET_EVENT_ARCH);
            assert forall |data: &[u8], a: u32|
                #![trigger Builder::goes_to(b.rev@, data, b.rev@.len(), a, body.len(), Event::of(data).nr as u32)]
                #![trigger Builder::goes_to(b.rev@, data, b.rev@.len(), a, end as nat, Event::of(data).arch)]
                Event::parse(data) is Some implies
                if Event::of(data).arch == self.token() {
                    Builder::goes_to(b.rev@, data, b.rev@.len(), a,
                        body.len(), Event::of(data).nr as u32)
                } else {
                    Builder::goes_to(b.rev@, data, b.rev@.len(), a,
                        end as nat, Event::of(data).arch)
                } by {
                let ev = Event::of(data);
                let nr = ev.nr as u32;
                let to = if ev.arch == self.token() { body.len() } else { end as nat };
                Event::lemma_image(data);
                if ev.arch == self.token() {
                    assert(Builder::goes_to(loaded_nr, data, loaded_nr.len(), ev.arch, body.len(), nr));
                    Builder::lemma_then(loaded_nr, guarded_arch, data, guarded_arch.len(), ev.arch,
                        loaded_nr.len(), ev.arch, to, nr);
                    Builder::lemma_then(guarded_arch, b.rev@, data, b.rev@.len(), a,
                        guarded_arch.len(), ev.arch, to, nr);
                } else {
                    Builder::lemma_then(guarded_arch, b.rev@, data, b.rev@.len(), a,
                        guarded_arch.len(), ev.arch, to, ev.arch);
                }
            }
        }
        Ok(())
    }
}

impl Policy {
    /// Emits the rules and default return for an architecture token.
    ///
    /// ```text
    ///     <architecture guard> -> end
    ///     <rules by descending precedence and descending index>
    ///     ret #act_no_match
    /// end:
    /// ```
    pub(super) fn emit_arch_block(&self, b: &mut Builder, arch: Arch) -> (res: Result<(), CompileError>)
        requires self.wf(), 0 < b.rev@.len(), b.wf()
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], tail: Action| Event::parse(data) is Some
                && #[trigger] Builder::returns_all(old(b).rev@, data, old(b).rev@.len(), tail.to_ret()) ==>
                Builder::returns_all(final(b).rev@, data, final(b).rev@.len(),
                    if Event::of(data).arch == arch.token() {
                        self.dispatch(arch, Event::of(data), 7, self.rules@.len() as int).to_ret()
                    } else { tail.to_ret() }),
    {
        let end = b.label();
        let ghost prev = b.rev@;
        self.emit_arch(b, arch)?;
        let ghost body = b.rev@;
        arch.emit_guard(b, end)?;
        proof {
            assert forall |data: &[u8], tail: Action| Event::parse(data) is Some
                && #[trigger] Builder::returns_all(prev, data, prev.len(), tail.to_ret()) implies
                Builder::returns_all(b.rev@, data, b.rev@.len(),
                    if Event::of(data).arch == arch.token() {
                        self.dispatch(arch, Event::of(data), 7, self.rules@.len() as int).to_ret()
                    } else { tail.to_ret() }) by {
                let ev = Event::of(data);
                let want = if ev.arch == arch.token() {
                    self.dispatch(arch, ev, 7, self.rules@.len() as int).to_ret()
                } else { tail.to_ret() };
                assert forall |a: u32| #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), a, want) by {
                    if ev.arch == arch.token() {
                        assert(Builder::goes_to_all(b.rev@, data, b.rev@.len(), body.len(), ev.nr as u32));
                        Builder::lemma_then(body, b.rev@, data, b.rev@.len(), a, body.len(), ev.nr as u32, 0, want);
                    } else {
                        assert(Builder::goes_to_all(b.rev@, data, b.rev@.len(), prev.len(), ev.arch));
                        Builder::lemma_then(prev, b.rev@, data, b.rev@.len(), a, prev.len(), ev.arch, 0, want);
                    }
                }
            }
        }
        Ok(())
    }

    /// Emits an architecture's rules and default return in descending precedence and reverse insertion order.
    fn emit_arch(&self, b: &mut Builder, arch: Arch) -> (res: Result<(), CompileError>)
        requires self.wf(), 0 < b.rev@.len(), b.wf()
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8]| Event::parse(data) is Some ==>
                #[trigger] Builder::returns(final(b).rev@, data, final(b).rev@.len(),
                    Event::of(data).nr as u32,
                    self.dispatch(arch, Event::of(data), 7, self.rules@.len() as int).to_ret()),
    {
        b.emit(Instr::Ret(RetVal::K(self.act_no_match.to_ret())));
        proof { Builder::lemma_ret(b.rev@, self.act_no_match.to_ret()); }
        // The builder runs backward: low precedence and early rules are emitted first.
        let mut priority: u8 = 0;
        proof {
            assert forall |data: &[u8]| Event::parse(data) is Some implies
                #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                    self.dispatch(arch, Event::of(data), -1, self.rules@.len() as int).to_ret()) by {
                assert(Builder::returns_all(b.rev@, data, b.rev@.len(), self.act_no_match.to_ret()));
            }
        }
        while priority < 8
            invariant
                priority <= 8,
                self.wf(), b.wf(), 0 < b.rev@.len(),
                Builder::extends(old(b).rev@, b.rev@),
                forall |data: &[u8]| Event::parse(data) is Some ==>
                    #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                        self.dispatch(arch, Event::of(data), priority - 1, self.rules@.len() as int).to_ret()),
            decreases 8 - priority
        {
            let mut i: usize = 0;
            proof {
                assert forall |data: &[u8]| Event::parse(data) is Some implies
                    #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                        self.dispatch(arch, Event::of(data), priority as int, 0).to_ret()) by {
                    assert(Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                        self.dispatch(arch, Event::of(data), priority - 1, self.rules@.len() as int).to_ret()));
                }
            }
            while i < self.rules.len()
                invariant
                    priority < 8,
                    i <= self.rules@.len(),
                    self.wf(), b.wf(), 0 < b.rev@.len(),
                    Builder::extends(old(b).rev@, b.rev@),
                    forall |data: &[u8]| Event::parse(data) is Some ==>
                        #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                            self.dispatch(arch, Event::of(data), priority as int, i as int).to_ret()),
                decreases self.rules@.len() - i
            {
                assert(self.rules@[i as int].wf());
                let ghost prev = b.rev@;
                let ghost rule = self.rules@[i as int];
                if self.rules[i].action.priority() == priority {
                    self.rules[i].emit_tests(b, arch)?;
                }
                proof {
                    assert forall |data: &[u8]| Event::parse(data) is Some implies
                        #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                            self.dispatch(arch, Event::of(data), priority as int, i + 1).to_ret()) by {
                        let ev = Event::of(data);
                        let nr = ev.nr as u32;
                        let want = self.dispatch(arch, ev, priority as int, i + 1).to_ret();
                        if rule.action.precedence() != priority || !rule.eval(arch, ev) {
                            assert(Builder::goes_to(b.rev@, data, b.rev@.len(), nr, prev.len(), nr));
                            assert(Builder::returns(prev, data, prev.len(), nr,
                                self.dispatch(arch, ev, priority as int, i as int).to_ret()));
                            Builder::lemma_then(prev, b.rev@, data, b.rev@.len(), nr, prev.len(), nr, 0, want);
                        }
                    }
                }
                i += 1;
            }
            priority += 1;
        }
        proof {
            assert forall |data: &[u8]| Event::parse(data) is Some implies
                #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                    self.dispatch(arch, Event::of(data), 7, self.rules@.len() as int).to_ret()) by {
                assert(Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                    self.dispatch(arch, Event::of(data), priority - 1, self.rules@.len() as int).to_ret()));
            }
        }
        Ok(())
    }
}

} // verus!
