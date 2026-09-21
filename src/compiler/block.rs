//! Compiling one architecture's block: the guard that claims an event, and the dispatch
//! of the policy's rules under it.

use vstd::prelude::*;
use crate::spec::{policy::*, cbpf::*};
use super::CompileError;
use super::builder::{Builder, Label};

verus! {

impl Arch {
    /// `AUDIT_ARCH_*` in `linux/audit.h`: what the kernel reports in
    /// `seccomp_data.arch`. x86_64 and x32 are one and the same token.
    pub const TOKEN_X86: u32 = 0x4000_0003;
    pub const TOKEN_X86_64: u32 = 0xC000_003E;
    pub const TOKEN_ARM: u32 = 0x4000_0028;
    pub const TOKEN_AARCH64: u32 = 0xC000_00B7;

    /// `X32_SYSCALL_BIT` (`src/arch-x32.h`), as the filter's unsigned comparisons
    /// see it.
    const X32_SYSCALL_BIT: u32 = 0x4000_0000;

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

    /// Emits the syscall-number guard for x32.
    ///
    /// ```text
    ///     jlt #X32_SYSCALL_BIT -> end        ; x32 only
    /// ```
    fn emit_x32_guard(self, b: &mut Builder, end: Label) -> (res: Result<(), CompileError>)
        requires 0 < end <= b.rev@.len(), b.wf()
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE
                && self.admits(Event::of(data)) ==>
                #[trigger] Builder::goes_to(final(b).rev@, data, final(b).rev@.len(),
                    Event::of(data).nr as u32, old(b).rev@.len(), Event::of(data).nr as u32),
            res is Ok ==> forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE
                && !self.admits(Event::of(data)) ==>
                #[trigger] Builder::goes_to(final(b).rev@, data, final(b).rev@.len(),
                    Event::of(data).nr as u32, end as nat, Event::of(data).nr as u32),
    {
        if self == Arch::X32 {
            b.emit_jump(JmpOp::Ge, Src::K(Self::X32_SYSCALL_BIT), false, end)?;
            proof {
                assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE implies
                    #[trigger] Event::of(data).x32_bit()
                        == (Event::of(data).nr as u32 >= Self::X32_SYSCALL_BIT) by {
                    Event::lemma_nr(Event::of(data));
                }
            }
        } else {
            proof {
                assert forall |data: &[u8], a: u32| true implies
                    #[trigger] Builder::goes_to(b.rev@, data, b.rev@.len(), a,
                        b.rev@.len(), a) by {
                }
            }
        }
        Ok(())
    }

    /// Emits the architecture guard and loads the syscall number on a match.
    ///
    /// ```text
    ///     ld  [arch]
    ///     jne #token -> end
    ///     ld  [nr]
    ///     <x32 bit guard> -> end
    /// ```
    fn emit_guard(self, b: &mut Builder, end: Label) -> (res: Result<(), CompileError>)
        requires 0 < end <= b.rev@.len(), b.wf()
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE
                && Event::of(data).matches_arch(self) && self.admits(Event::of(data)) ==>
                #[trigger] Builder::goes_to_all(final(b).rev@, data, final(b).rev@.len(),
                    old(b).rev@.len(), Event::of(data).nr as u32),
            res is Ok ==> forall |data: &[u8], a: u32| data@.len() == Program::SECCOMP_DATA_SIZE
                && !(Event::of(data).matches_arch(self) && self.admits(Event::of(data))) ==>
                #[trigger] Builder::lands(final(b).rev@, data, final(b).rev@.len(), a, end as nat),
    {
        let ghost body = b.rev@;
        self.emit_x32_guard(b, end)?;
        let ghost s1 = b.rev@;
        b.emit(Instr::LdAbs(Policy::OFFSET_EVENT_NR))?;
        proof { Builder::lemma_ld(b.rev@, Policy::OFFSET_EVENT_NR); }
        let ghost s2 = b.rev@;
        b.emit_jump(JmpOp::Eq, Src::K(self.token()), false, end)?;
        let ghost s3 = b.rev@;
        b.emit(Instr::LdAbs(Policy::OFFSET_EVENT_ARCH))?;
        proof {
            Builder::lemma_ld(b.rev@, Policy::OFFSET_EVENT_ARCH);
            assert forall |data: &[u8], a: u32|
                #![trigger Builder::goes_to(b.rev@, data, b.rev@.len(), a, body.len(), Event::of(data).nr as u32)]
                #![trigger Builder::goes_to(b.rev@, data, b.rev@.len(), a, end as nat, Event::of(data).nr as u32)]
                #![trigger Builder::goes_to(b.rev@, data, b.rev@.len(), a, end as nat, Event::of(data).arch)]
                data@.len() == Program::SECCOMP_DATA_SIZE implies
                if Event::of(data).matches_arch(self) && self.admits(Event::of(data)) {
                    Builder::goes_to(b.rev@, data, b.rev@.len(), a,
                        body.len(), Event::of(data).nr as u32)
                } else if Event::of(data).matches_arch(self) {
                    Builder::goes_to(b.rev@, data, b.rev@.len(), a,
                        end as nat, Event::of(data).nr as u32)
                } else {
                    Builder::goes_to(b.rev@, data, b.rev@.len(), a,
                        end as nat, Event::of(data).arch)
                } by {
                let ev = Event::of(data);
                let nr = ev.nr as u32;
                let to = if ev.matches_arch(self) && self.admits(ev) { body.len() } else { end as nat };
                Event::lemma_image(data);
                if ev.matches_arch(self) {
                    assert(Builder::goes_to(s1, data, s1.len(), nr, to, nr));
                    assert(Builder::goes_to(s2, data, s2.len(), ev.arch, s1.len(), nr));
                    Builder::lemma_then(s1, s2, data, s2.len(), ev.arch, s1.len(), nr, to, nr);
                    Builder::lemma_then(s2, s3, data, s3.len(), ev.arch, s2.len(), ev.arch, to, nr);
                    Builder::lemma_then(s3, b.rev@, data, b.rev@.len(), a, s3.len(), ev.arch, to, nr);
                } else {
                    Builder::lemma_then(s3, b.rev@, data, b.rev@.len(), a, s3.len(), ev.arch, to, ev.arch);
                }
            }
            assert forall |data: &[u8], a: u32| data@.len() == Program::SECCOMP_DATA_SIZE
                && !(Event::of(data).matches_arch(self) && self.admits(Event::of(data))) implies
                #[trigger] Builder::lands(b.rev@, data, b.rev@.len(), a, end as nat) by {
                let ev = Event::of(data);
                let m = if ev.matches_arch(self) { ev.nr as u32 } else { ev.arch };
                assert(Builder::goes_to(b.rev@, data, b.rev@.len(), a, end as nat, m));
            }
        }
        Ok(())
    }
}

impl Policy {
    /// Whether the policy covers `arch`.
    fn has_arch(&self, arch: Arch) -> (res: bool)
        ensures res == self.archs@.contains(arch)
    {
        let mut i = 0;
        while i < self.archs.len()
            invariant
                i <= self.archs@.len(),
                forall |j: int| 0 <= j < i ==> self.archs@[j] != arch,
            decreases self.archs@.len() - i
        {
            if self.archs[i] == arch {
                return true;
            }
            i += 1;
        }
        false
    }

    /// Emits the rules and default return for an architecture token.
    ///
    /// ```text
    ///     <architecture guard> -> end
    ///     <rules by descending precedence and descending index>
    ///     ret #act_default
    /// end:
    /// ```
    pub(super) fn emit_arch_block(&self, b: &mut Builder, arch: Arch) -> (res: Result<(), CompileError>)
        requires self.wf(), 0 < b.rev@.len(), b.wf()
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], tail: Action| data@.len() == Program::SECCOMP_DATA_SIZE
                && #[trigger] Builder::returns_all(old(b).rev@, data, old(b).rev@.len(), tail.to_ret()) ==>
                Builder::returns_all(final(b).rev@, data, final(b).rev@.len(),
                    if self.takes(arch, Event::of(data)) {
                        self.dispatch(arch, Event::of(data), 8, self.rules@.len() as int).to_ret()
                    } else { tail.to_ret() }),
    {
        if arch == Arch::X32 && self.has_arch(Arch::X86_64) {
            return Ok(());
        }
        let end = b.label();
        let ghost prev = b.rev@;
        b.emit(Instr::Ret(RetVal::K(self.attrs.act_default.to_ret())))?;
        proof { Builder::lemma_ret(b.rev@, self.attrs.act_default.to_ret()); }
        self.emit_arch(b, arch)?;
        let ghost body = b.rev@;
        arch.emit_guard(b, end)?;
        proof {
            assert forall |data: &[u8], tail: Action| data@.len() == Program::SECCOMP_DATA_SIZE
                && #[trigger] Builder::returns_all(prev, data, prev.len(), tail.to_ret()) implies
                Builder::returns_all(b.rev@, data, b.rev@.len(),
                    if self.takes(arch, Event::of(data)) {
                        self.dispatch(arch, Event::of(data), 8, self.rules@.len() as int).to_ret()
                    } else { tail.to_ret() }) by {
                let ev = Event::of(data);
                let want = if self.takes(arch, ev) {
                    self.dispatch(arch, ev, 8, self.rules@.len() as int).to_ret()
                } else { tail.to_ret() };
                assert forall |a: u32| #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), a, want) by {
                    if self.takes(arch, ev) {
                        assert(Builder::goes_to_all(b.rev@, data, b.rev@.len(), body.len(), ev.nr as u32));
                        Builder::lemma_then(body, b.rev@, data, b.rev@.len(), a, body.len(), ev.nr as u32, 0, want);
                    } else {
                        Builder::lemma_then_any(prev, b.rev@, data, b.rev@.len(), a, prev.len(), 0, want);
                    }
                }
            }
        }
        Ok(())
    }

    /// Emits the rules sharing an architecture token in descending precedence and reverse insertion order.
    fn emit_arch(&self, b: &mut Builder, arch: Arch) -> (res: Result<(), CompileError>)
        requires
            self.wf(), 0 < b.rev@.len(), b.wf(),
            forall |data: &[u8]| #[trigger] Builder::returns_all(b.rev@, data, b.rev@.len(),
                self.attrs.act_default.to_ret()),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE ==>
                #[trigger] Builder::returns(final(b).rev@, data, final(b).rev@.len(),
                    Event::of(data).nr as u32,
                    self.dispatch(arch, Event::of(data), 8, self.rules@.len() as int).to_ret()),
    {
        let has_x32 = self.has_arch(Arch::X32);
        // The builder runs backward: low precedence and early rules are emitted first.
        let mut priority: u8 = 0;
        proof {
            assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE implies
                #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                    self.dispatch(arch, Event::of(data), -1, self.rules@.len() as int).to_ret()) by {
                assert(Builder::returns_all(b.rev@, data, b.rev@.len(), self.attrs.act_default.to_ret()));
            }
        }
        while priority <= 8
            invariant
                priority <= 9,
                self.wf(), b.wf(), 0 < b.rev@.len(),
                has_x32 == self.archs@.contains(Arch::X32),
                Builder::extends(old(b).rev@, b.rev@),
                forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE ==>
                    #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                        self.dispatch(arch, Event::of(data), priority - 1, self.rules@.len() as int).to_ret()),
            decreases 9 - priority
        {
            let mut i: usize = 0;
            proof {
                assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE implies
                    #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                        self.dispatch(arch, Event::of(data), priority as int, 0).to_ret()) by {
                    assert(Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                        self.dispatch(arch, Event::of(data), priority - 1, self.rules@.len() as int).to_ret()));
                }
            }
            while i < self.rules.len()
                invariant
                    priority <= 8,
                    i <= self.rules@.len(),
                    self.wf(), b.wf(), 0 < b.rev@.len(),
                    has_x32 == self.archs@.contains(Arch::X32),
                    Builder::extends(old(b).rev@, b.rev@),
                    forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE ==>
                        #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                            self.dispatch(arch, Event::of(data), priority as int, i as int).to_ret()),
                decreases self.rules@.len() - i
            {
                assert(self.rules@[i as int].wf(self.attrs));
                let ghost prev = b.rev@;
                let ghost rule = self.rules@[i as int];
                if self.rules[i].action.priority() == priority {
                    if arch == Arch::X86_64 && has_x32 {
                        self.rules[i].emit_tests(b, Arch::X32)?;
                    }
                    let ghost x32 = b.rev@;
                    self.rules[i].emit_tests(b, arch)?;
                    proof {
                        assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE implies
                            #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                                self.dispatch(arch, Event::of(data), priority as int, i + 1).to_ret()) by {
                            let ev = Event::of(data);
                            let nr = ev.nr as u32;
                            let want = self.dispatch(arch, ev, priority as int, i + 1).to_ret();
                            if !rule.eval(arch, ev) {
                                assert(Builder::goes_to(b.rev@, data, b.rev@.len(), nr, x32.len(), nr));
                                if arch == Arch::X86_64 && has_x32 && rule.eval(Arch::X32, ev) {
                                    assert(Builder::returns(x32, data, x32.len(), nr, rule.action.to_ret()));
                                } else {
                                    assert(Builder::goes_to(x32, data, x32.len(), nr, prev.len(), nr));
                                    assert(Builder::returns(prev, data, prev.len(), nr,
                                        self.dispatch(arch, ev, priority as int, i as int).to_ret()));
                                    Builder::lemma_then(prev, x32, data, x32.len(), nr, prev.len(), nr, 0, want);
                                }
                                Builder::lemma_then(x32, b.rev@, data, b.rev@.len(), nr, x32.len(), nr, 0, want);
                            }
                        }
                    }
                } else {
                    proof {
                        assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE implies
                            #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                                self.dispatch(arch, Event::of(data), priority as int, i + 1).to_ret()) by {
                            assert(Builder::returns(prev, data, prev.len(), Event::of(data).nr as u32,
                                self.dispatch(arch, Event::of(data), priority as int, i as int).to_ret()));
                        }
                    }
                }
                i += 1;
            }
            priority += 1;
        }
        proof {
            assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE implies
                #[trigger] Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                    self.dispatch(arch, Event::of(data), 8, self.rules@.len() as int).to_ret()) by {
                assert(Builder::returns(b.rev@, data, b.rev@.len(), Event::of(data).nr as u32,
                    self.dispatch(arch, Event::of(data), priority - 1, self.rules@.len() as int).to_ret()));
            }
        }
        Ok(())
    }
}

} // verus!
