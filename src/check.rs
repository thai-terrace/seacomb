//! Policy validation (i.e., executable versions of the `wf` specs).

use vstd::prelude::*;
use crate::spec::{policy::*, syscall::*};

verus! {

/// An error while validating a filter policy.
#[verifier::external_derive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum CheckError {
    /// Invalid errno number.
    #[error("invalid errno number {0}")]
    InvalidErrno(u16),
    /// Invalid argument index for a syscall signature.
    #[error("argument index {given} is out of range for {syscall:?} ({total} arguments)")]
    InvalidArg { given: u32, total: u32, syscall: Syscall },
    /// A comparison operator is incompatible with an argument type.
    #[error("operator {op:?} is unsupported for {ty:?} argument {arg} of {syscall:?}")]
    UnsupportedCompare { arg: u32, syscall: Syscall, ty: PrimType, op: Compare },
    /// A comparison value does not fit an argument type.
    #[error("value {value:#x} does not fit {ty:?} argument {arg} of {syscall:?}")]
    InvalidCompareValue { arg: u32, syscall: Syscall, ty: PrimType, value: u64 },
    /// A comparison mask does not fit an argument type.
    #[error("mask {mask:#x} does not fit {ty:?} argument {arg} of {syscall:?}")]
    InvalidCompareMask { arg: u32, syscall: Syscall, ty: PrimType, mask: u64 },
    /// A masked comparison value has bits outside its mask.
    #[error("value {value:#x} exceeds mask {mask:#x} for {ty:?} argument {arg} of {syscall:?}")]
    InvalidMaskedValue { arg: u32, syscall: Syscall, ty: PrimType, mask: u64, value: u64 },
    /// A rule has conditions on a syscall whose signatures differ across architectures.
    #[error("syscall signatures differ across enabled architectures")]
    IncompatSigs,
    /// A multiplexed syscall rule cannot have argument conditions.
    #[error("multiplexed syscall rule cannot have argument conditions; use add_rule_exact")]
    InvalidMuxConditions,
    /// The filter already includes this architecture.
    #[error("filter already includes this architecture")]
    DuplicateArch,
}

impl Action {
    /// Checks whether this action contains a valid value.
    pub(crate) fn check(&self) -> (res: Result<(), CheckError>)
        ensures (res is Ok) == self.wf()
    {
        match self {
            Action::Errno(e) if (*e as u32) > Self::MAX_ERRNO => Err(CheckError::InvalidErrno(*e)),
            _ => Ok(()),
        }
    }
}

impl ArgCmp {
    /// Checks a condition against one syscall signature.
    pub(crate) fn check(&self, arch: Arch, syscall: Syscall, sig: &[PrimType]) -> (res: Result<(), CheckError>)
        requires sig@ =~= syscall.spec_signature(arch)
        ensures res is Ok ==> self.wf(arch, syscall)
    {
        if self.arg as usize >= sig.len() {
            return Err(CheckError::InvalidArg {
                given: self.arg, total: sig.len() as u32, syscall,
            });
        }
        let ty = sig[self.arg as usize];
        let mask = ty.exec_mask(arch);
        let order = self.op == Compare::Lt || self.op == Compare::Le
            || self.op == Compare::Gt || self.op == Compare::Ge;
        if ty == PrimType::Ptr && order {
            return Err(CheckError::UnsupportedCompare { arg: self.arg, syscall, ty, op: self.op });
        }
        if self.op == Compare::MaskedEq {
            if self.a & !mask != 0 {
                return Err(CheckError::InvalidCompareMask { arg: self.arg, syscall, ty, mask: self.a });
            }
            if self.b & !self.a != 0 {
                return Err(CheckError::InvalidMaskedValue {
                    arg: self.arg, syscall, ty, mask: self.a, value: self.b,
                });
            }
        } else if ty.exec_signed() {
            let sign = !(mask >> 1);
            if self.a & sign != 0 && self.a & sign != sign {
                return Err(CheckError::InvalidCompareValue {
                    arg: self.arg, syscall, ty, value: self.a,
                });
            }
        } else if self.a & !mask != 0 {
            return Err(CheckError::InvalidCompareValue {
                arg: self.arg, syscall, ty, value: self.a,
            });
        }
        Ok(())
    }
}

impl Rule {
    /// Checks the rule against every enabled architecture.
    pub(crate) fn check(&self, archs: &[Arch]) -> (res: Result<(), CheckError>)
        ensures res is Ok ==> self.wf(archs@)
    {
        self.action.check()?;
        if !self.no_mux && !self.conds.is_empty()
            && (self.syscall.socketcall_arg().is_some() || self.syscall.ipc_arg().is_some()) {
            return Err(CheckError::InvalidMuxConditions);
        }
        if self.conds.is_empty() {
            return Ok(());
        }
        if archs.is_empty() {
            return Ok(());
        }
        let first = self.syscall.signature(archs[0]);
        let mut i: usize = 0;
        while i < archs.len()
            invariant
                self.action.wf(),
                !self.no_mux && self.syscall.can_mux() ==> self.conds@.len() == 0,
                0 < archs@.len(),
                first@ =~= self.syscall.spec_signature(archs@[0]),
                i <= archs@.len(),
                forall |k: int| 0 <= k < i ==>
                    self.syscall.spec_signature(#[trigger] archs@[k]) =~= first@,
                forall |k: int, l: int| 0 <= k < i && 0 <= l < self.conds@.len()
                    ==> #[trigger] self.conds@[l].wf(archs@[k], self.syscall),
            decreases archs@.len() - i
        {
            let arch = archs[i];
            let sig = self.syscall.signature(arch);
            if sig.len() != first.len() {
                return Err(CheckError::IncompatSigs);
            }
            let mut t: usize = 0;
            while t < sig.len()
                invariant
                    t <= sig@.len(),
                    sig@.len() == first@.len(),
                    forall |k: int| 0 <= k < t ==> sig@[k] == first@[k],
                decreases sig@.len() - t
            {
                if sig[t] != first[t] {
                    return Err(CheckError::IncompatSigs);
                }
                t += 1;
            }
            proof {
                assert(sig@ =~= first@);
            }
            let mut j: usize = 0;
            while j < self.conds.len()
                invariant
                    j <= self.conds@.len(),
                    sig@ =~= self.syscall.spec_signature(arch),
                    forall |l: int| 0 <= l < j ==>
                        #[trigger] self.conds@[l].wf(arch, self.syscall),
                decreases self.conds@.len() - j
            {
                self.conds[j].check(arch, self.syscall, sig)?;
                j += 1;
            }
            proof {
                assert(self.syscall.spec_signature(arch) =~= first@);
                assert forall |k: int, l: int| 0 <= k < i + 1 && 0 <= l < self.conds@.len()
                    implies #[trigger] self.conds@[l].wf(archs@[k], self.syscall) by {
                    if k == i {
                        assert(archs@[k] == arch);
                    }
                }
            }
            i += 1;
        }
        proof {
            assert forall |k: int, l: int| #![trigger archs@[k], archs@[l]] 0 <= k < l < archs@.len()
                && self.syscall.spec_signature(archs@[k])
                    != self.syscall.spec_signature(archs@[l])
                implies self.conds@.len() == 0 by {
                assert(self.syscall.spec_signature(archs@[k]) =~= first@);
                assert(self.syscall.spec_signature(archs@[l]) =~= first@);
            }
        }
        Ok(())
    }
}

} // verus!
