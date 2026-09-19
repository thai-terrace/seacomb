//! Abstract syntax and semantics of classic BPF (cBPF) programs.

use vstd::prelude::*;

verus! {

/// Width of a packet load (`BPF_SIZE`): `BPF_W`, `BPF_H`, `BPF_B`.
pub enum Size { W, H, B }

/// Second operand of ALU and conditional jump instructions (`BPF_SRC`): `BPF_K`, `BPF_X`.
pub enum Src { K(u32), X }

/// Return value (`BPF_RVAL`): `BPF_K`, `BPF_A`.
pub enum RetVal { K(u32), A }

/// ALU operator (`BPF_OP` of class `BPF_ALU`, except `BPF_NEG`).
pub enum AluOp { Add, Sub, Mul, Div, Or, And, Lsh, Rsh, Mod, Xor }

/// Comparison of a conditional jump (`BPF_OP` of class `BPF_JMP`, except `BPF_JA`); unsigned.
pub enum JmpOp { Eq, Gt, Ge, Set }

/// `struct sock_filter`.
pub enum Instr {
    /// `BPF_LD | size | BPF_ABS`: `A = P[k:size]`.
    LdAbs(Size, u32),
    /// `BPF_LD | size | BPF_IND`: `A = P[X + k:size]`.
    LdInd(Size, u32),
    /// `BPF_LD | BPF_W | BPF_LEN`: `A = len`.
    LdLen,
    /// `BPF_LD | BPF_IMM`: `A = k`.
    LdImm(u32),
    /// `BPF_LD | BPF_MEM`: `A = M[k]`.
    LdMem(u32),
    /// `BPF_LDX | BPF_W | BPF_LEN`: `X = len`.
    LdxLen,
    /// `BPF_LDX | BPF_IMM`: `X = k`.
    LdxImm(u32),
    /// `BPF_LDX | BPF_MEM`: `X = M[k]`.
    LdxMem(u32),
    /// `BPF_LDX | BPF_B | BPF_MSH`: `X = 4 * (P[k:1] & 0xf)`.
    LdxMsh(u32),
    /// `BPF_ST`: `M[k] = A`.
    St(u32),
    /// `BPF_STX`: `M[k] = X`.
    Stx(u32),
    /// `BPF_ALU | op | src`: `A = A op src`.
    Alu(AluOp, Src),
    /// `BPF_ALU | BPF_NEG`: `A = -A`.
    Neg,
    /// `BPF_JMP | BPF_JA`: skip `k` instructions.
    Ja(u32),
    /// `BPF_JMP | op | src`: skip `jt` instructions if `A op src` holds, else `jf`.
    Jmp { op: JmpOp, src: Src, jt: u8, jf: u8 },
    /// `BPF_RET | rval`: return `rval`.
    Ret(RetVal),
    /// `BPF_MISC | BPF_TAX`: `X = A`.
    Tax,
    /// `BPF_MISC | BPF_TXA`: `A = X`.
    Txa,
}

/// `struct sock_fprog`.
pub struct Program {
    pub instrs: Seq<Instr>,
}

impl Instr {
    pub open spec fn wf(self, pc: nat, max_pc: nat) -> bool {
        match self {
            // Check for division by zero.
            Instr::Alu(AluOp::Div, Src::K(k)) => k != 0,
            Instr::Alu(AluOp::Mod, Src::K(k)) => k != 0,
            Instr::Alu(AluOp::Lsh, Src::K(k)) => k < 32,
            Instr::Alu(AluOp::Rsh, Src::K(k)) => k < 32,
            // Check for invalid memory addresses.
            Instr::LdMem(k) => k < Program::MEM_WORDS,
            Instr::LdxMem(k) => k < Program::MEM_WORDS,
            Instr::St(k) => k < Program::MEM_WORDS,
            Instr::Stx(k) => k < Program::MEM_WORDS,
            // Jump targets stay inside the program.
            Instr::Ja(k) => pc + 1 + k < max_pc,
            Instr::Jmp { jt, jf, .. } => pc + 1 + jt < max_pc && pc + 1 + jf < max_pc,
            _ => true,
        }
    }
}

impl Program {
    /// `BPF_MAXINSNS` in `linux/filter.h`.
    pub const MAX_INSTRS: u32 = 4096;

    /// `BPF_MEMWORDS` in `linux/filter.h`.
    pub const MEM_WORDS: u32 = 16;

    /// `bpf_check_classic` in `net/core/filter.c`, without `SKF_AD_*` and `check_load_and_stores` checks.
    pub open spec fn wf(self) -> bool {
        &&& 0 < self.instrs.len() <= Self::MAX_INSTRS as int
        &&& self.instrs.last() is Ret
        &&& forall |pc: int| #![trigger self.instrs[pc]]
                0 <= pc < self.instrs.len() ==> self.instrs[pc].wf(pc as nat, self.instrs.len())
    }
}

} // verus!
