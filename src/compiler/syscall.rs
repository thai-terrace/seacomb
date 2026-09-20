//! The syscall numbers and multiplexer arguments a filter compares against.

use vstd::prelude::*;
use crate::spec::policy::*;

verus! {

impl SyscallName {
    /// Executable version of [`SyscallName::to_socketcall_arg`].
    pub fn socketcall_arg(&self) -> (res: Option<u64>)
        ensures res == self.to_socketcall_arg()
    {
        match self {
            SyscallName::Socket       => Some(1),
            SyscallName::Bind         => Some(2),
            SyscallName::Connect      => Some(3),
            SyscallName::Listen       => Some(4),
            SyscallName::Accept       => Some(5),
            SyscallName::Getsockname  => Some(6),
            SyscallName::Getpeername  => Some(7),
            SyscallName::Socketpair   => Some(8),
            SyscallName::Send         => Some(9),
            SyscallName::Recv         => Some(10),
            SyscallName::Sendto       => Some(11),
            SyscallName::Recvfrom     => Some(12),
            SyscallName::Shutdown     => Some(13),
            SyscallName::Setsockopt   => Some(14),
            SyscallName::Getsockopt   => Some(15),
            SyscallName::Sendmsg      => Some(16),
            SyscallName::Recvmsg      => Some(17),
            SyscallName::Accept4      => Some(18),
            SyscallName::Recvmmsg     => Some(19),
            SyscallName::Sendmmsg     => Some(20),
            _ => None,
        }
    }

    /// Executable version of [`SyscallName::to_ipc_arg`].
    pub fn ipc_arg(&self) -> (res: Option<u64>)
        ensures res == self.to_ipc_arg()
    {
        match self {
            SyscallName::Semop        => Some(1),
            SyscallName::Semget       => Some(2),
            SyscallName::Semctl       => Some(3),
            SyscallName::Semtimedop   => Some(4),
            SyscallName::Msgsnd       => Some(11),
            SyscallName::Msgrcv       => Some(12),
            SyscallName::Msgget       => Some(13),
            SyscallName::Msgctl       => Some(14),
            SyscallName::Shmat        => Some(21),
            SyscallName::Shmdt        => Some(22),
            SyscallName::Shmget       => Some(23),
            SyscallName::Shmctl       => Some(24),
            _ => None,
        }
    }
}

impl Syscall {
    /// The syscall number at which `arch` reaches this syscall, as the filter's
    /// unsigned comparisons see it, if it reaches it at all.
    pub(super) open spec fn spec_nr(&self, arch: Arch) -> Option<u32> {
        match self {
            Syscall::Skip => Some(Event::SKIP_NR as u32),
            Syscall::Name(name) => match name.spec_nr(arch) {
                Some(nr) => Some(nr as u32),
                None => None,
            },
        }
    }

    /// Executable version of [`Syscall::spec_nr`].
    #[verifier::when_used_as_spec(spec_nr)]
    pub(super) fn nr(&self, arch: Arch) -> (res: Option<u32>)
        ensures res == self.spec_nr(arch)
    {
        match self {
            Syscall::Skip => Some(Event::SKIP_NR as u32),
            Syscall::Name(name) => match name.nr(arch) {
                Some(nr) => Some(nr as u32),
                None => None,
            },
        }
    }
}

} // verus!
