//! Encoding the instructions of a filter program into the kernel's `struct sock_filter`.

use vstd::prelude::*;
use crate::spec::cbpf::*;

verus! {

/// `struct sock_filter` in `linux/filter.h`.
#[repr(C)]
pub struct SockFilter {
    pub code: u16,
    pub jt: u8,
    pub jf: u8,
    pub k: u32,
}

impl Src {
    /// The `BPF_SRC` bit of this operand.
    fn code(&self) -> u16 {
        match self {
            Src::K(_) => 0x00,  // BPF_K
            Src::X => 0x08,     // BPF_X
        }
    }

    /// The immediate this operand puts in `sock_filter.k`.
    fn k(&self) -> u32 {
        match self {
            Src::K(k) => *k,
            Src::X => 0,
        }
    }
}

impl RetVal {
    /// The `BPF_RVAL` bit of this return value.
    fn code(&self) -> u16 {
        match self {
            RetVal::K(_) => 0x00,  // BPF_K
            RetVal::A => 0x10,     // BPF_A
        }
    }

    /// The immediate this return value puts in `sock_filter.k`.
    fn k(&self) -> u32 {
        match self {
            RetVal::K(k) => *k,
            RetVal::A => 0,
        }
    }
}

impl Instr {
    const BPF_LD: u16 = 0x00;
    const BPF_LDX: u16 = 0x01;
    const BPF_ST: u16 = 0x02;
    const BPF_STX: u16 = 0x03;
    const BPF_ALU: u16 = 0x04;
    const BPF_JMP: u16 = 0x05;
    const BPF_RET: u16 = 0x06;
    const BPF_MISC: u16 = 0x07;

    const BPF_W: u16 = 0x00;

    const BPF_IMM: u16 = 0x00;
    const BPF_ABS: u16 = 0x20;
    const BPF_MEM: u16 = 0x60;
    const BPF_LEN: u16 = 0x80;

    const BPF_NEG: u16 = 0x80;
    const BPF_JA: u16 = 0x00;

    const BPF_TAX: u16 = 0x00;
    const BPF_TXA: u16 = 0x80;

    fn assemble(&self) -> SockFilter {
        let (code, jt, jf, k) = match self {
            Instr::LdAbs(k) => (Self::BPF_LD | Self::BPF_W | Self::BPF_ABS, 0, 0, *k),
            Instr::LdLen => (Self::BPF_LD | Self::BPF_W | Self::BPF_LEN, 0, 0, 0),
            Instr::LdImm(k) => (Self::BPF_LD | Self::BPF_W | Self::BPF_IMM, 0, 0, *k),
            Instr::LdMem(k) => (Self::BPF_LD | Self::BPF_W | Self::BPF_MEM, 0, 0, *k),
            Instr::LdxLen => (Self::BPF_LDX | Self::BPF_W | Self::BPF_LEN, 0, 0, 0),
            Instr::LdxImm(k) => (Self::BPF_LDX | Self::BPF_W | Self::BPF_IMM, 0, 0, *k),
            Instr::LdxMem(k) => (Self::BPF_LDX | Self::BPF_W | Self::BPF_MEM, 0, 0, *k),
            Instr::St(k) => (Self::BPF_ST, 0, 0, *k),
            Instr::Stx(k) => (Self::BPF_STX, 0, 0, *k),
            Instr::Alu(op, src) => (Self::BPF_ALU | *op as u16 | src.code(), 0, 0, src.k()),
            Instr::Neg => (Self::BPF_ALU | Self::BPF_NEG, 0, 0, 0),
            Instr::Ja(k) => (Self::BPF_JMP | Self::BPF_JA, 0, 0, *k),
            Instr::Jmp { op, src, jt, jf } => (Self::BPF_JMP | *op as u16 | src.code(), *jt, *jf, src.k()),
            Instr::Ret(rval) => (Self::BPF_RET | rval.code(), 0, 0, rval.k()),
            Instr::Tax => (Self::BPF_MISC | Self::BPF_TAX, 0, 0, 0),
            Instr::Txa => (Self::BPF_MISC | Self::BPF_TXA, 0, 0, 0),
        };
        SockFilter { code, jt, jf, k }
    }
}

impl Program {
    /// The `struct sock_filter` array this program assembles to.
    pub fn assemble(&self) -> Vec<SockFilter> {
        let mut filter = Vec::with_capacity(self.instrs.len());
        let mut i: usize = 0;
        while i < self.instrs.len()
            invariant i <= self.instrs@.len()
            decreases self.instrs@.len() - i
        {
            filter.push(self.instrs[i].assemble());
            i += 1;
        }
        filter
    }
}

} // verus!
