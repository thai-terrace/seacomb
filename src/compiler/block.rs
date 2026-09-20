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

    /// Emits the guard that tells apart the x86_64 and x32 syscalls.
    ///
    /// ```text
    ///     jeq #-1              -> dispatch   ; x86_64 without x32: the skip pseudo-syscall
    ///     jge #X32_SYSCALL_BIT -> end        ;   carries the bit but stays in scope
    /// ```
    /// ```text
    ///     jge #X32_SYSCALL_BIT -> end        ; x86_64 beside x32, which claims the skip
    /// ```
    /// ```text
    ///     jlt #X32_SYSCALL_BIT -> end        ; x32
    /// ```
    fn emit_x32_guard(self, b: &mut Builder, end: Label, has_x32: bool) -> (res: Result<(), CompileError>)
        requires 0 < end <= b.rev@.len(), b.wf()
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE
                && self.admits(Event::of(data), has_x32) ==>
                #[trigger] Builder::goes_to(final(b).rev@, data, final(b).rev@.len(),
                    Event::of(data).nr as u32, old(b).rev@.len(), Event::of(data).nr as u32),
            res is Ok ==> forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE
                && !self.admits(Event::of(data), has_x32) ==>
                #[trigger] Builder::goes_to(final(b).rev@, data, final(b).rev@.len(),
                    Event::of(data).nr as u32, end as nat, Event::of(data).nr as u32),
    {
        let pass = b.label();
        match self {
            Arch::X86_64 => {
                b.emit_jump(JmpOp::Ge, Src::K(Self::X32_SYSCALL_BIT), true, end)?;
                let ghost bit_test = b.rev@;
                if has_x32 {
                    proof {
                        assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE implies
                            #[trigger] Event::of(data).x32_bit()
                                == (Event::of(data).nr as u32 >= Self::X32_SYSCALL_BIT) by {
                            Event::lemma_nr(Event::of(data));
                        }
                    }
                    return Ok(());
                }
                b.emit_jump(JmpOp::Eq, Src::K(Event::SKIP_NR as u32), true, pass)?;
                proof {
                    assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE
                        && self.admits(Event::of(data), has_x32) implies
                        #[trigger] Builder::goes_to(b.rev@, data, b.rev@.len(),
                            Event::of(data).nr as u32, pass as nat, Event::of(data).nr as u32) by {
                        let a = Event::of(data).nr as u32;
                        Event::lemma_nr(Event::of(data));
                        if a != Event::SKIP_NR as u32 {
                            Builder::lemma_then(bit_test, b.rev@, data, b.rev@.len(), a,
                                bit_test.len(), a, pass as nat, a);
                        }
                    }
                    assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE
                        && !self.admits(Event::of(data), has_x32) implies
                        #[trigger] Builder::goes_to(b.rev@, data, b.rev@.len(),
                            Event::of(data).nr as u32, end as nat, Event::of(data).nr as u32) by {
                        let a = Event::of(data).nr as u32;
                        Event::lemma_nr(Event::of(data));
                        Builder::lemma_then(bit_test, b.rev@, data, b.rev@.len(), a,
                            bit_test.len(), a, end as nat, a);
                    }
                }
                Ok(())
            }
            Arch::X32 => {
                b.emit_jump(JmpOp::Ge, Src::K(Self::X32_SYSCALL_BIT), false, end)?;
                proof {
                    assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE implies
                        #[trigger] Event::of(data).x32_bit()
                            == (Event::of(data).nr as u32 >= Self::X32_SYSCALL_BIT) by {
                        Event::lemma_nr(Event::of(data));
                    }
                }
                Ok(())
            }
            _ => {
                proof {
                    assert forall |data: &[u8], a: u32| true implies
                        #[trigger] Builder::goes_to(b.rev@, data, b.rev@.len(), a,
                            b.rev@.len(), a) by {
                    }
                }
                Ok(())
            }
        }
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

    /// Emits the block handling `arch`.
    ///
    /// Forward layout:
    ///
    /// ```text
    ///     ld  [arch]
    ///     jne #token -> end
    ///     ld  [nr]
    ///     <x32 bit guard> -> end      ; only where one is needed
    ///     <dispatch of arch>
    ///     ret #act_default
    /// end:
    /// ```
    pub(super) fn emit_arch_block(&self, b: &mut Builder, arch: Arch) -> (res: Result<(), CompileError>)
        requires self.wf(), 0 < b.rev@.len(), b.wf()
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8], tail: u32| data@.len() == Program::SECCOMP_DATA_SIZE
                && #[trigger] Builder::returns_all(old(b).rev@, data, old(b).rev@.len(), tail)
                && self.takes(arch, Event::of(data)) ==>
                Builder::returns_all(final(b).rev@, data, final(b).rev@.len(),
                    self.dispatch(arch, Event::of(data), 0).to_ret()),
            res is Ok ==> forall |data: &[u8], tail: u32| data@.len() == Program::SECCOMP_DATA_SIZE
                && #[trigger] Builder::returns_all(old(b).rev@, data, old(b).rev@.len(), tail)
                && !self.takes(arch, Event::of(data)) ==>
                Builder::returns_all(final(b).rev@, data, final(b).rev@.len(), tail),
    {
        let end = b.label();
        let ghost s0 = b.rev@;
        b.emit(Instr::Ret(RetVal::K(self.attrs.act_default.to_ret())))?;
        proof { Builder::lemma_ret(b.rev@, self.attrs.act_default.to_ret()); }
        self.emit_arch(b, arch)?;
        let ghost s2 = b.rev@;
        arch.emit_x32_guard(b, end, self.has_arch(Arch::X32))?;
        let ghost s3 = b.rev@;
        b.emit(Instr::LdAbs(Self::OFFSET_EVENT_NR))?;
        proof { Builder::lemma_ld(b.rev@, Self::OFFSET_EVENT_NR); }
        let ghost s4 = b.rev@;
        b.emit_jump(JmpOp::Eq, Src::K(arch.token()), false, end)?;
        let ghost s5 = b.rev@;
        let ghost s6 = s5.push(Instr::LdAbs(Self::OFFSET_EVENT_ARCH));
        proof {
            Builder::lemma_ld(s6, Self::OFFSET_EVENT_ARCH);
            assert forall |data: &[u8], tail: u32| data@.len() == Program::SECCOMP_DATA_SIZE
                && #[trigger] Builder::returns_all(s0, data, s0.len(), tail)
                implies Builder::returns_all(s6, data, s6.len(),
                    if self.takes(arch, Event::of(data)) {
                        self.dispatch(arch, Event::of(data), 0).to_ret()
                    } else {
                        tail
                    }) by {
                let ev = Event::of(data);
                let nr = ev.nr as u32;
                let want = if self.takes(arch, ev) { self.dispatch(arch, ev, 0).to_ret() } else { tail };
                Event::lemma_image(data);
                assert forall |a: u32| #[trigger] Builder::returns(s6, data, s6.len(), a, want) by {
                    assert(Builder::goes_to_all(s6, data, s6.len(), s5.len(),
                        Builder::word(data, Self::OFFSET_EVENT_ARCH)));
                    assert(Builder::goes_to(s6, data, s6.len(), a, s5.len(), ev.arch));
                    if ev.matches_arch(arch) {
                        assert(Builder::goes_to(s5, data, s5.len(), ev.arch, s4.len(), ev.arch));
                        assert(Builder::goes_to_all(s4, data, s4.len(), s3.len(),
                            Builder::word(data, Self::OFFSET_EVENT_NR)));
                        assert(Builder::goes_to(s4, data, s4.len(), ev.arch, s3.len(), nr));
                        if arch.admits(ev, self.archs@.contains(Arch::X32)) {
                            assert(Builder::goes_to(s3, data, s3.len(), nr, s2.len(), nr));
                            assert(Builder::returns(s2, data, s2.len(), nr, want));
                            Builder::lemma_then(s2, s3, data, s3.len(), nr, s2.len(), nr, 0, want);
                        } else {
                            assert(Builder::goes_to(s3, data, s3.len(), nr, end as nat, nr));
                            assert(Builder::returns(s0, data, s0.len(), nr, want));
                            Builder::lemma_then(s0, s3, data, s3.len(), nr, end as nat, nr, 0, want);
                        }
                        Builder::lemma_then(s3, s4, data, s4.len(), ev.arch, s3.len(), nr, 0, want);
                        Builder::lemma_then(s4, s5, data, s5.len(), ev.arch, s4.len(), ev.arch, 0, want);
                    } else {
                        assert(Builder::goes_to(s5, data, s5.len(), ev.arch, end as nat, ev.arch));
                        assert(Builder::returns(s0, data, s0.len(), ev.arch, want));
                        Builder::lemma_then(s0, s5, data, s5.len(), ev.arch, end as nat, ev.arch, 0, want);
                    }
                    Builder::lemma_then(s5, s6, data, s6.len(), a, s5.len(), ev.arch, 0, want);
                }
                assert(Builder::returns_all(s6, data, s6.len(), want));
            }
        }
        b.emit(Instr::LdAbs(Self::OFFSET_EVENT_ARCH))
    }

    /// Emits the dispatch of one architecture, entered with `A` holding
    /// `seccomp_data.nr` and falling through when no rule of `arch` matches the event.
    fn emit_arch(&self, b: &mut Builder, arch: Arch) -> (res: Result<(), CompileError>)
        requires
            self.wf(),
            0 < b.rev@.len(),
            b.wf(),
            forall |data: &[u8]| #[trigger] Builder::returns_all(b.rev@, data, b.rev@.len(),
                self.attrs.act_default.to_ret()),
        ensures
            Builder::extends(old(b).rev@, final(b).rev@),
            final(b).wf(),
            res is Ok ==> forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE ==>
                #[trigger] Builder::returns(final(b).rev@, data, final(b).rev@.len(),
                    Event::of(data).nr as u32, self.dispatch(arch, Event::of(data), 0).to_ret()),
    {
        // One test per rule, in the policy's order. Only the last of them falls through
        // to the block's default return, so every earlier one has to hand `A` back.
        let mut a_live = false;
        let mut i = self.rules.len();
        // With no test emitted yet the block still falls through to its default return.
        proof {
            assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE implies
                #[trigger] Builder::returns(b.rev@, data, b.rev@.len(),
                    Event::of(data).nr as u32,
                    self.dispatch(arch, Event::of(data), i as int).to_ret()) by {
                assert(Builder::returns_all(b.rev@, data, b.rev@.len(),
                    self.attrs.act_default.to_ret()));
            }
        }
        while i > 0
            invariant
                i <= self.rules@.len(),
                self.wf(),
                b.wf(),
                0 < old(b).rev@.len(),
                Builder::extends(old(b).rev@, b.rev@),
                !a_live ==> b.rev@ == old(b).rev@,
                forall |data: &[u8]| #[trigger] Builder::returns_all(old(b).rev@, data,
                    old(b).rev@.len(), self.attrs.act_default.to_ret()),
                forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE ==>
                    #[trigger] Builder::returns(b.rev@, data, b.rev@.len(),
                        Event::of(data).nr as u32, self.dispatch(arch, Event::of(data), i as int).to_ret()),
            decreases i
        {
            i -= 1;
            assert(self.rules@[i as int].wf(self.attrs));
            let ghost r = self.rules@[i as int];
            let ghost i0 = i as int + 1;
            let ghost prev0 = b.rev@;
            let ghost live0 = a_live;

            // x86 reaches some rules a second time through the socketcall or ipc
            // multiplexer, which answers to a number of its own.
            if let Some(nr) = self.rules[i].mux_nr(arch) {
                self.rules[i].emit(b, arch, nr, a_live)?;
                a_live = true;
            }
            let ghost s1 = b.rev@;
            let ghost live1 = a_live;
            // The multiplexer test returns the rule's action, or hands control back.
            proof {
                assert(Builder::extends(prev0, s1));
                assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE
                    && (match r.spec_mux_nr(arch) {
                        Some(m) => r.matches_at(arch, m, Event::of(data)),
                        None => false,
                    })
                    implies #[trigger] Builder::returns(s1, data, s1.len(),
                        Event::of(data).nr as u32, r.action.to_ret()) by {
                    Event::lemma_image(data);
                }
                if live0 {
                    assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE
                        && !(match r.spec_mux_nr(arch) {
                            Some(m) => r.matches_at(arch, m, Event::of(data)),
                            None => false,
                        })
                        implies #[trigger] Builder::goes_to(s1, data, s1.len(),
                            Event::of(data).nr as u32, prev0.len(),
                            Event::of(data).nr as u32) by {
                        Event::lemma_image(data);
                    }
                } else {
                    assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE
                        && !(match r.spec_mux_nr(arch) {
                            Some(m) => r.matches_at(arch, m, Event::of(data)),
                            None => false,
                        })
                        implies #[trigger] Builder::lands(s1, data, s1.len(),
                            Event::of(data).nr as u32, prev0.len()) by {
                        Event::lemma_image(data);
                        if s1 == prev0 {
                            assert(Builder::goes_to(s1, data, s1.len(),
                                Event::of(data).nr as u32, prev0.len(),
                                Event::of(data).nr as u32));
                        }
                    }
                }
            }
            if let Some(nr) = self.rules[i].syscall.nr(arch) {
                self.rules[i].emit(b, arch, nr, a_live)?;
                a_live = true;
            }
            // The syscall's own test returns the rule's action, or hands control back.
            proof {
                assert(Builder::extends(s1, b.rev@));
                assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE
                    && (match r.syscall.spec_nr(arch) {
                        Some(m) => r.matches_at(arch, m, Event::of(data)),
                        None => false,
                    })
                    implies #[trigger] Builder::returns(b.rev@, data, b.rev@.len(),
                        Event::of(data).nr as u32, r.action.to_ret()) by {
                    Event::lemma_image(data);
                }
                if live1 {
                    assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE
                        && !(match r.syscall.spec_nr(arch) {
                            Some(m) => r.matches_at(arch, m, Event::of(data)),
                            None => false,
                        })
                        implies #[trigger] Builder::goes_to(b.rev@, data, b.rev@.len(),
                            Event::of(data).nr as u32, s1.len(),
                            Event::of(data).nr as u32) by {
                        Event::lemma_image(data);
                    }
                } else {
                    assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE
                        && !(match r.syscall.spec_nr(arch) {
                            Some(m) => r.matches_at(arch, m, Event::of(data)),
                            None => false,
                        })
                        implies #[trigger] Builder::lands(b.rev@, data, b.rev@.len(),
                            Event::of(data).nr as u32, s1.len()) by {
                        Event::lemma_image(data);
                        if b.rev@ == s1 {
                            assert(Builder::goes_to(b.rev@, data, b.rev@.len(),
                                Event::of(data).nr as u32, s1.len(),
                                Event::of(data).nr as u32));
                        }
                    }
                }
            }
            // Either test reaching the rule settles the dispatch on its action, and
            // neither reaching it leaves the dispatch of the rules behind it.
            proof {
                assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE implies
                    #[trigger] Builder::returns(b.rev@, data, b.rev@.len(),
                        Event::of(data).nr as u32,
                        self.dispatch(arch, Event::of(data), i as int).to_ret()) by {
                    let ev = Event::of(data);
                    let n = ev.nr as u32;
                    let c_mux = match r.spec_mux_nr(arch) {
                        Some(m) => r.matches_at(arch, m, ev),
                        None => false,
                    };
                    let c_own = match r.syscall.spec_nr(arch) {
                        Some(m) => r.matches_at(arch, m, ev),
                        None => false,
                    };
                    Event::lemma_image(data);
                    r.lemma_matches(arch, ev);
                    if c_own {
                        assert(r.matches(arch, ev));
                        assert(Builder::returns(b.rev@, data, b.rev@.len(), n,
                            r.action.to_ret()));
                    } else if c_mux {
                        assert(r.matches(arch, ev));
                        assert(Builder::returns(s1, data, s1.len(), n, r.action.to_ret()));
                        assert(Builder::goes_to(b.rev@, data, b.rev@.len(), n, s1.len(), n));
                        Builder::lemma_then(s1, b.rev@, data, b.rev@.len(), n, s1.len(), n,
                            0, r.action.to_ret());
                    } else {
                        assert(!r.matches(arch, ev));
                        let want = self.dispatch(arch, ev, i0).to_ret();
                        assert(Builder::returns(prev0, data, prev0.len(), n, want));
                        if live1 {
                            if live0 {
                                assert(Builder::goes_to(s1, data, s1.len(), n, prev0.len(), n));
                                Builder::lemma_then(prev0, s1, data, s1.len(), n,
                                    prev0.len(), n, 0, want);
                            } else {
                                assert(Builder::returns_all(prev0, data, prev0.len(),
                                    self.attrs.act_default.to_ret()));
                                assert(Builder::returns(prev0, data, prev0.len(), n,
                                    self.attrs.act_default.to_ret()));
                                assert(Builder::extends(prev0, prev0));
                                assert(Builder::run(prev0, data, prev0.len(), n)
                                    == Outcome::Return(self.attrs.act_default.to_ret()));
                                assert(Builder::run(prev0, data, prev0.len(), n)
                                    == Outcome::Return(want));
                                assert(Builder::returns_all(prev0, data, prev0.len(), want));
                                assert(Builder::lands(s1, data, s1.len(), n, prev0.len()));
                                Builder::lemma_then_any(prev0, s1, data, s1.len(), n,
                                    prev0.len(), 0, want);
                            }
                            assert(Builder::goes_to(b.rev@, data, b.rev@.len(), n, s1.len(), n));
                            Builder::lemma_then(s1, b.rev@, data, b.rev@.len(), n, s1.len(), n,
                                0, want);
                        } else {
                            assert(s1 == prev0);
                            assert(Builder::returns_all(prev0, data, prev0.len(),
                                self.attrs.act_default.to_ret()));
                            assert(Builder::returns(prev0, data, prev0.len(), n,
                                self.attrs.act_default.to_ret()));
                            assert(Builder::extends(prev0, prev0));
                            assert(Builder::run(prev0, data, prev0.len(), n)
                                == Outcome::Return(self.attrs.act_default.to_ret()));
                            assert(Builder::run(prev0, data, prev0.len(), n)
                                == Outcome::Return(want));
                            assert(Builder::returns_all(s1, data, s1.len(), want));
                            assert(Builder::lands(b.rev@, data, b.rev@.len(), n, s1.len()));
                            Builder::lemma_then_any(s1, b.rev@, data, b.rev@.len(), n,
                                s1.len(), 0, want);
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

} // verus!
