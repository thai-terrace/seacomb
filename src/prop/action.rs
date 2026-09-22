//! Supporting facts about action encodings and precedence.

use vstd::prelude::*;
use crate::spec::policy::Action;

verus! {

impl Action {
    /// Encoding keeps the action code and payload in separate fields.
    proof fn lemma_ret_parts(self)
        ensures
            self.to_ret() & Self::RET_ACTION == match self {
                Action::KillProcess => Self::RET_KILL_PROCESS,
                Action::KillThread => Self::RET_KILL_THREAD,
                Action::Trap(_) => Self::RET_TRAP,
                Action::Errno(_) => Self::RET_ERRNO,
                Action::Notify => Self::RET_USER_NOTIF,
                Action::Trace(_) => Self::RET_TRACE,
                Action::Log => Self::RET_LOG,
                Action::Allow => Self::RET_ALLOW,
            },
            self.to_ret() & Self::RET_DATA == match self {
                Action::Trap(data) | Action::Errno(data) | Action::Trace(data) => data as u32,
                _ => 0u32,
            },
    {
        let code = match self {
            Action::KillProcess => Self::RET_KILL_PROCESS,
            Action::KillThread => Self::RET_KILL_THREAD,
            Action::Trap(_) => Self::RET_TRAP,
            Action::Errno(_) => Self::RET_ERRNO,
            Action::Notify => Self::RET_USER_NOTIF,
            Action::Trace(_) => Self::RET_TRACE,
            Action::Log => Self::RET_LOG,
            Action::Allow => Self::RET_ALLOW,
        };
        let data = match self {
            Action::Trap(data) | Action::Errno(data) | Action::Trace(data) => data,
            _ => 0u16,
        };
        assert(code & 0xffff_0000u32 == code) by (bit_vector)
            requires code == 0x8000_0000u32 || code == 0x0000_0000u32
                || code == 0x0003_0000u32 || code == 0x0005_0000u32
                || code == 0x7fc0_0000u32 || code == 0x7ff0_0000u32
                || code == 0x7ffc_0000u32 || code == 0x7fff_0000u32;
        assert(code | 0u32 == code) by (bit_vector);
        assert((code | data as u32) & 0xffff_0000u32 == code
            && (code | data as u32) & 0x0000_ffffu32 == data as u32) by (bit_vector)
            requires code & 0xffff_0000u32 == code;
    }

    /// Equal encodings identify the same action, including its payload.
    pub(super) proof fn lemma_to_ret_injective(a: Action, b: Action)
        ensures (a.to_ret() == b.to_ret()) <==> a == b
    {
        a.lemma_ret_parts();
        b.lemma_ret_parts();
    }

    /// Signed action-code ordering agrees with abstract action precedence.
    pub(super) proof fn lemma_ret_precedence(a: Action, b: Action)
        ensures
            (((a.to_ret() & Self::RET_ACTION) as i32) < ((b.to_ret() & Self::RET_ACTION) as i32))
                <==> a.precedence() > b.precedence(),
            (((a.to_ret() & Self::RET_ACTION) as i32) == ((b.to_ret() & Self::RET_ACTION) as i32))
                <==> a.precedence() == b.precedence(),
    {
        a.lemma_ret_parts();
        b.lemma_ret_parts();
        assert(0x8000_0000u32 as i32 == -2147483648i32) by (bit_vector);
    }
}

} // verus!
