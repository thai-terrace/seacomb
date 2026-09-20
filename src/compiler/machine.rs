//! The filter as the builder sees it, addressed by labels instead of program counters.
//!
//! A label counts instructions back from the end of the program, so it names the same
//! program point however much is later emitted in front of it, and a fact proved about
//! the instructions emitted so far still holds of the whole program.

use vstd::prelude::*;
use crate::spec::cbpf::*;
use super::builder::Builder;

verus! {

impl Instr {
    /// Whether the instruction reads nothing but `data` and `A`, as everything the
    /// compiler emits does.
    pub(super) open spec fn simple(self) -> bool {
        match self {
            Instr::LdAbs(_) => true,
            Instr::Alu(_, Src::K(_)) => true,
            Instr::Ja(_) => true,
            Instr::Jmp { src: Src::K(_), .. } => true,
            Instr::Ret(RetVal::K(_)) => true,
            _ => false,
        }
    }

    /// Every instruction moves the program counter forward.
    pub(super) proof fn lemma_advances(self, data: &[u8], st: MachineState)
        ensures self.step(data, st) matches Ok(next) ==> next.pc > st.pc
    {
    }

    /// A simple instruction leaves `X` and scratch memory alone, and neither what it
    /// puts in `A` nor how far it moves the program counter depends on either of those
    /// or on where the instruction sits.
    pub(super) proof fn lemma_simple(self, data: &[u8], st: MachineState, other: MachineState)
        requires self.simple(), st.a == other.a
        ensures
            self.step(data, st) matches Ok(next) ==> {
                &&& self.step(data, other) matches Ok(then)
                &&& next.a == then.a
                &&& next.pc - st.pc == then.pc - other.pc
                &&& next.x == st.x
                &&& next.mem == st.mem
            },
            self.step(data, st) matches Err(outcome)
                ==> self.step(data, other) == Err::<MachineState, Outcome>(outcome),
    {
    }
}

impl Builder {
    /// Whether `ext` is `rev` with more instructions emitted in front of it.
    pub(super) open spec fn extends(rev: Seq<Instr>, ext: Seq<Instr>) -> bool {
        &&& rev.len() <= ext.len()
        &&& forall |i: int| #![trigger ext[i]] 0 <= i < rev.len() ==> ext[i] == rev[i]
    }

    /// The little-endian word at byte offset `k` of `data`, as `LdAbs` reads it.
    pub(super) open spec fn word(data: &[u8], k: u32) -> u32 {
        (data@[k as int] as u32)
            | ((data@[k + 1] as u32) << 8)
            | ((data@[k + 2] as u32) << 16)
            | ((data@[k + 3] as u32) << 24)
    }

    /// Runs the instructions emitted so far, entered `label` of them before their end
    /// with `A` holding `a`.
    pub(super) open spec fn run(rev: Seq<Instr>, data: &[u8], label: nat, a: u32) -> Outcome
        decreases label
        via Self::run_decreases
    {
        if label == 0 || label > rev.len() {
            Outcome::RuntimeError
        } else {
            match rev[label - 1].step(data, Self::state(label, a)) {
                Ok(next) =>
                    if next.pc > 2 * label {
                        Outcome::RuntimeError
                    } else {
                        Self::run(rev, data, (2 * label - next.pc) as nat, next.a)
                    },
                Err(outcome) => outcome,
            }
        }
    }

    /// The machine state [`Builder::run`] hands an instruction at `label`.
    pub(super) open spec fn state(label: nat, a: u32) -> MachineState {
        MachineState { pc: label, a, x: 0, mem: Seq::empty() }
    }

    #[via_fn]
    proof fn run_decreases(rev: Seq<Instr>, data: &[u8], label: nat, a: u32) {
        if label != 0 && label <= rev.len() {
            rev[label - 1].lemma_advances(data, Self::state(label, a));
        }
    }

    /// Whether every extension of `rev`, entered at `from` with `A` holding `a`,
    /// carries on at `to` with `A` holding `b`.
    pub(super) open spec fn goes_to(rev: Seq<Instr>, data: &[u8], from: nat, a: u32, to: nat, b: u32) -> bool {
        forall |ext: Seq<Instr>| Self::extends(rev, ext)
            ==> #[trigger] Self::run(ext, data, from, a) == Self::run(ext, data, to, b)
    }

    /// Whether every extension of `rev`, entered at `from` whatever `A` holds, carries
    /// on at `to` with `A` holding `b`.
    pub(super) open spec fn goes_to_all(rev: Seq<Instr>, data: &[u8], from: nat, to: nat, b: u32) -> bool {
        forall |a: u32| #[trigger] Self::goes_to(rev, data, from, a, to, b)
    }

    /// Whether every extension of `rev`, entered at `from` with `A` holding `a`, carries
    /// on at `to`, with nothing left to say about `A`.
    pub(super) open spec fn lands(rev: Seq<Instr>, data: &[u8], from: nat, a: u32, to: nat) -> bool {
        exists |b: u32| Self::goes_to(rev, data, from, a, to, b)
    }

    /// Whether every extension of `rev`, entered at `from` with `A` holding `a`, returns `ret`.
    pub(super) open spec fn returns(rev: Seq<Instr>, data: &[u8], from: nat, a: u32, ret: u32) -> bool {
        forall |ext: Seq<Instr>| Self::extends(rev, ext)
            ==> #[trigger] Self::run(ext, data, from, a) == Outcome::Return(ret)
    }

    /// Whether every extension of `rev`, entered at `from` whatever `A` holds, returns `ret`.
    pub(super) open spec fn returns_all(rev: Seq<Instr>, data: &[u8], from: nat, ret: u32) -> bool {
        forall |a: u32| #[trigger] Self::returns(rev, data, from, a, ret)
    }

    /// Whether the instruction `i` slots back from the end of the program belongs there.
    pub(super) open spec fn instr_ok(instr: Instr, i: nat) -> bool {
        &&& instr.simple()
        &&& match instr {
            Instr::LdAbs(k) => k < Program::SECCOMP_DATA_SIZE && k % 4 == 0,
            Instr::Alu(AluOp::Div, Src::K(k)) => k != 0,
            Instr::Alu(AluOp::Lsh, Src::K(k)) => k < 32,
            Instr::Alu(AluOp::Rsh, Src::K(k)) => k < 32,
            Instr::Ja(k) => k < i,
            Instr::Jmp { jt, jf, .. } => jt < i && jf < i,
            _ => true,
        }
    }

    /// Whether the instructions emitted so far can end a well-formed program.
    pub(super) open spec fn wf(self) -> bool {
        &&& self.rev@.len() <= Program::MAX_INSTRS
        &&& forall |i: int| #![trigger self.rev@[i]]
                0 <= i < self.rev@.len() ==> Self::instr_ok(self.rev@[i], i as nat)
    }

    /// A well-formed buffer whose first instruction returns makes a well-formed program.
    pub(super) proof fn lemma_wf(self, prog: Program)
        requires
            self.wf(),
            0 < self.rev@.len(),
            self.rev@[0] is Ret,
            prog.instrs@ == self.rev@.reverse(),
        ensures
            prog.wf(),
            prog.instrs@.reverse() == self.rev@,
            forall |i: int| 0 <= i < prog.instrs@.len() ==> #[trigger] prog.instrs@[i].simple(),
    {
        let len = self.rev@.len();
        assert forall |pc: int| #![trigger prog.instrs@[pc]] 0 <= pc < len implies
            prog.instrs@[pc].wf(pc as nat, len) && prog.instrs@[pc].simple() by {
            assert(Self::instr_ok(self.rev@[len - 1 - pc], (len - 1 - pc) as nat));
        }
        assert(prog.instrs@.reverse() =~= self.rev@);
    }

    /// Facts about the instructions emitted so far hold of anything emitted in front of them.
    pub(super) proof fn lemma_mono(rev: Seq<Instr>, ext: Seq<Instr>, data: &[u8], from: nat, a: u32, to: nat, b: u32)
        requires Self::extends(rev, ext)
        ensures
            Self::goes_to(rev, data, from, a, to, b) ==> Self::goes_to(ext, data, from, a, to, b),
            Self::lands(rev, data, from, a, to) ==> Self::lands(ext, data, from, a, to),
            Self::returns(rev, data, from, a, b) ==> Self::returns(ext, data, from, a, b),
    {
        assert forall |far: Seq<Instr>| Self::extends(ext, far) implies Self::extends(rev, far) by {
        }
        if Self::goes_to(rev, data, from, a, to, b) {
            assert forall |far: Seq<Instr>| Self::extends(ext, far) implies
                #[trigger] Self::run(far, data, from, a) == Self::run(far, data, to, b) by {
            }
        }
        if Self::lands(rev, data, from, a, to) {
            let c = choose |c: u32| Self::goes_to(rev, data, from, a, to, c);
            assert forall |far: Seq<Instr>| Self::extends(ext, far) implies
                #[trigger] Self::run(far, data, from, a) == Self::run(far, data, to, c) by {
            }
            assert(Self::goes_to(ext, data, from, a, to, c));
        }
        if Self::returns(rev, data, from, a, b) {
            assert forall |far: Seq<Instr>| Self::extends(ext, far) implies
                #[trigger] Self::run(far, data, from, a) == Outcome::Return(b) by {
            }
        }
    }

    /// Entering `from` runs the stretch of code that reaches `mid` and then the one behind it.
    pub(super) proof fn lemma_then(rev: Seq<Instr>, ext: Seq<Instr>, data: &[u8], from: nat, a: u32, mid: nat, m: u32, to: nat, b: u32)
        requires
            Self::extends(rev, ext),
            Self::goes_to(ext, data, from, a, mid, m),
        ensures
            Self::goes_to(rev, data, mid, m, to, b) ==> Self::goes_to(ext, data, from, a, to, b),
            Self::lands(rev, data, mid, m, to) ==> Self::lands(ext, data, from, a, to),
            Self::returns(rev, data, mid, m, b) ==> Self::returns(ext, data, from, a, b),
    {
        assert forall |far: Seq<Instr>| Self::extends(ext, far) implies Self::extends(rev, far) by {
        }
        if Self::goes_to(rev, data, mid, m, to, b) {
            assert forall |far: Seq<Instr>| Self::extends(ext, far) implies
                #[trigger] Self::run(far, data, from, a) == Self::run(far, data, to, b) by {
            }
        }
        if Self::lands(rev, data, mid, m, to) {
            let c = choose |c: u32| Self::goes_to(rev, data, mid, m, to, c);
            assert forall |far: Seq<Instr>| Self::extends(ext, far) implies
                #[trigger] Self::run(far, data, from, a) == Self::run(far, data, to, c) by {
            }
            assert(Self::goes_to(ext, data, from, a, to, c));
        }
        if Self::returns(rev, data, mid, m, b) {
            assert forall |far: Seq<Instr>| Self::extends(ext, far) implies
                #[trigger] Self::run(far, data, from, a) == Outcome::Return(b) by {
            }
        }
    }

    /// Entering `from` reaches `mid`, where what `A` holds no longer matters.
    pub(super) proof fn lemma_then_any(rev: Seq<Instr>, ext: Seq<Instr>, data: &[u8], from: nat, a: u32, mid: nat, to: nat, b: u32)
        requires
            Self::extends(rev, ext),
            Self::lands(ext, data, from, a, mid),
        ensures
            Self::goes_to_all(rev, data, mid, to, b) ==> Self::goes_to(ext, data, from, a, to, b),
            Self::returns_all(rev, data, mid, b) ==> Self::returns(ext, data, from, a, b),
    {
        let m = choose |m: u32| Self::goes_to(ext, data, from, a, mid, m);
        if Self::goes_to_all(rev, data, mid, to, b) {
            assert(Self::goes_to(rev, data, mid, m, to, b));
            Self::lemma_then(rev, ext, data, from, a, mid, m, to, b);
        }
        if Self::returns_all(rev, data, mid, b) {
            assert(Self::returns(rev, data, mid, m, b));
            Self::lemma_then(rev, ext, data, from, a, mid, m, to, b);
        }
    }

    /// The load at the front of `rev` hands `A` the word at `k`.
    pub(super) proof fn lemma_ld(rev: Seq<Instr>, k: u32)
        requires
            0 < rev.len(),
            rev[rev.len() - 1] == Instr::LdAbs(k),
            k + 4 <= Program::SECCOMP_DATA_SIZE,
        ensures forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE ==>
            #[trigger] Self::goes_to_all(rev, data, rev.len(), (rev.len() - 1) as nat, Self::word(data, k))
    {
        assert forall |data: &[u8]| data@.len() == Program::SECCOMP_DATA_SIZE implies
            #[trigger] Self::goes_to_all(rev, data, rev.len(), (rev.len() - 1) as nat, Self::word(data, k)) by {
            assert forall |a: u32| #[trigger] Self::goes_to(rev, data, rev.len(), a,
                (rev.len() - 1) as nat, Self::word(data, k)) by {
                assert forall |ext: Seq<Instr>| Self::extends(rev, ext) implies
                    #[trigger] Self::run(ext, data, rev.len(), a)
                        == Self::run(ext, data, (rev.len() - 1) as nat, Self::word(data, k)) by {
                    assert(ext[rev.len() - 1] == Instr::LdAbs(k));
                }
            }
        }
    }

    /// The operation at the front of `rev` applies `op` to `A`.
    pub(super) proof fn lemma_alu(rev: Seq<Instr>, op: AluOp, k: u32)
        requires
            0 < rev.len(),
            rev[rev.len() - 1] == Instr::Alu(op, Src::K(k)),
            !(op is Div && k == 0),
        ensures forall |data: &[u8], a: u32|
            #[trigger] Self::goes_to(rev, data, rev.len(), a, (rev.len() - 1) as nat, op.eval(a, k))
    {
        assert forall |data: &[u8], a: u32|
            #[trigger] Self::goes_to(rev, data, rev.len(), a, (rev.len() - 1) as nat, op.eval(a, k)) by {
            assert forall |ext: Seq<Instr>| Self::extends(rev, ext) implies
                #[trigger] Self::run(ext, data, rev.len(), a)
                    == Self::run(ext, data, (rev.len() - 1) as nat, op.eval(a, k)) by {
                assert(ext[rev.len() - 1] == Instr::Alu(op, Src::K(k)));
            }
        }
    }

    /// The return at the front of `rev` ends the filter with `k`.
    pub(super) proof fn lemma_ret(rev: Seq<Instr>, k: u32)
        requires 0 < rev.len(), rev[rev.len() - 1] == Instr::Ret(RetVal::K(k))
        ensures forall |data: &[u8]| #[trigger] Self::returns_all(rev, data, rev.len(), k)
    {
        assert forall |data: &[u8]| #[trigger] Self::returns_all(rev, data, rev.len(), k) by {
            assert forall |a: u32| #[trigger] Self::returns(rev, data, rev.len(), a, k) by {
                assert forall |ext: Seq<Instr>| Self::extends(rev, ext) implies
                    #[trigger] Self::run(ext, data, rev.len(), a) == Outcome::Return(k) by {
                    assert(ext[rev.len() - 1] == Instr::Ret(RetVal::K(k)));
                }
            }
        }
    }

    /// The unconditional jump at the front of `rev` skips `k` instructions.
    pub(super) proof fn lemma_ja(rev: Seq<Instr>, k: u32)
        requires 0 < rev.len(), rev[rev.len() - 1] == Instr::Ja(k), k < rev.len() - 1
        ensures forall |data: &[u8], a: u32|
            #[trigger] Self::goes_to(rev, data, rev.len(), a, (rev.len() - 1 - k) as nat, a)
    {
        assert forall |data: &[u8], a: u32|
            #[trigger] Self::goes_to(rev, data, rev.len(), a, (rev.len() - 1 - k) as nat, a) by {
            assert forall |ext: Seq<Instr>| Self::extends(rev, ext) implies
                #[trigger] Self::run(ext, data, rev.len(), a)
                    == Self::run(ext, data, (rev.len() - 1 - k) as nat, a) by {
                assert(ext[rev.len() - 1] == Instr::Ja(k));
            }
        }
    }

    /// The conditional jump at the front of `rev` skips `jt` instructions when `A op k`
    /// holds and `jf` when it does not.
    pub(super) proof fn lemma_jmp(rev: Seq<Instr>, op: JmpOp, k: u32, jt: u8, jf: u8)
        requires
            0 < rev.len(),
            rev[rev.len() - 1] == (Instr::Jmp { op, src: Src::K(k), jt, jf }),
            jt < rev.len() - 1,
            jf < rev.len() - 1,
        ensures
            forall |data: &[u8], a: u32| op.eval(a, k) ==>
                #[trigger] Self::goes_to(rev, data, rev.len(), a, (rev.len() - 1 - jt) as nat, a),
            forall |data: &[u8], a: u32| !op.eval(a, k) ==>
                #[trigger] Self::goes_to(rev, data, rev.len(), a, (rev.len() - 1 - jf) as nat, a),
    {
        assert forall |data: &[u8], a: u32| op.eval(a, k) implies
            #[trigger] Self::goes_to(rev, data, rev.len(), a, (rev.len() - 1 - jt) as nat, a) by {
            assert forall |ext: Seq<Instr>| Self::extends(rev, ext) implies
                #[trigger] Self::run(ext, data, rev.len(), a)
                    == Self::run(ext, data, (rev.len() - 1 - jt) as nat, a) by {
                assert(ext[rev.len() - 1] == (Instr::Jmp { op, src: Src::K(k), jt, jf }));
            }
        }
        assert forall |data: &[u8], a: u32| !op.eval(a, k) implies
            #[trigger] Self::goes_to(rev, data, rev.len(), a, (rev.len() - 1 - jf) as nat, a) by {
            assert forall |ext: Seq<Instr>| Self::extends(rev, ext) implies
                #[trigger] Self::run(ext, data, rev.len(), a)
                    == Self::run(ext, data, (rev.len() - 1 - jf) as nat, a) by {
                assert(ext[rev.len() - 1] == (Instr::Jmp { op, src: Src::K(k), jt, jf }));
            }
        }
    }
}

impl Program {
    /// The filter's outcome from an arbitrary state, seen through the builder's labels.
    pub(super) proof fn lemma_run_from(self, data: &[u8], st: MachineState)
        requires
            self.wf(),
            st.pc <= self.instrs@.len(),
            forall |i: int| 0 <= i < self.instrs@.len() ==> #[trigger] self.instrs@[i].simple(),
        ensures self.eval_from(data, st)
            == Builder::run(self.instrs@.reverse(), data, (self.instrs@.len() - st.pc) as nat, st.a)
        decreases self.instrs@.len() - st.pc
    {
        let len = self.instrs@.len();
        if st.pc < len {
            let instr = self.instrs@[st.pc as int];
            instr.lemma_simple(data, st, Builder::state((len - st.pc) as nat, st.a));
            if instr.step(data, st) is Ok {
                self.lemma_run_from(data, instr.step(data, st)->Ok_0);
            }
        }
    }

    /// The filter's outcome, seen through the builder's labels.
    pub(super) proof fn lemma_run(self, data: &[u8])
        requires
            self.wf(),
            forall |i: int| 0 <= i < self.instrs@.len() ==> #[trigger] self.instrs@[i].simple(),
        ensures self.eval(data) == Builder::run(self.instrs@.reverse(), data, self.instrs@.len(), 0)
    {
        self.lemma_run_from(data, MachineState::init());
    }
}

} // verus!
