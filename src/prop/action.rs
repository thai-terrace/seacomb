//! Supporting facts about action encodings and precedence.

use vstd::prelude::*;
use crate::spec::policy::Action;

verus! {

impl Action {
    /// Action codes for which decoding preserves the kernel's precedence ordering.
    pub(super) open spec fn recognized_ret(ret: u32) -> bool {
        let code = ret & Self::RET_ACTION;
        code == Self::RET_KILL_PROCESS || code == Self::RET_KILL_THREAD
            || code == Self::RET_TRAP || code == Self::RET_ERRNO
            || code == Self::RET_USER_NOTIF || code == Self::RET_TRACE
            || code == Self::RET_LOG || code == Self::RET_ALLOW
    }

    pub(super) proof fn lemma_canonical_ret(ret: u32)
        requires ret == Self::from_ret(ret).to_ret()
        ensures Self::recognized_ret(ret)
    {
        assert(0x8000_0000u32 & 0xffff_0000u32 == 0x8000_0000u32) by (bit_vector);
    }

    pub(super) proof fn lemma_ret_precedence(a: u32, b: u32)
        requires Self::recognized_ret(a), Self::recognized_ret(b)
        ensures
            (((a & Self::RET_ACTION) as i32) < ((b & Self::RET_ACTION) as i32))
                <==> Self::from_ret(a).precedence() > Self::from_ret(b).precedence(),
            (((a & Self::RET_ACTION) as i32) == ((b & Self::RET_ACTION) as i32))
                <==> Self::from_ret(a).precedence() == Self::from_ret(b).precedence(),
    {
        assert(0x8000_0000u32 as i32 == -2147483648i32) by (bit_vector);
    }
}

} // verus!
