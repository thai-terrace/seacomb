//! The syscall numbers and multiplexer arguments a filter compares against.

use vstd::prelude::*;
use crate::spec::policy::*;
use crate::spec::syscall::*;

verus! {

impl Syscall {
    /// Executable version of [`Syscall::to_socketcall_arg`].
    pub(super) fn socketcall_arg(&self) -> (res: Option<u64>)
        ensures res == self.to_socketcall_arg()
    {
        match self {
            Syscall::Socket       => Some(1),
            Syscall::Bind         => Some(2),
            Syscall::Connect      => Some(3),
            Syscall::Listen       => Some(4),
            Syscall::Accept       => Some(5),
            Syscall::Getsockname  => Some(6),
            Syscall::Getpeername  => Some(7),
            Syscall::Socketpair   => Some(8),
            Syscall::Send         => Some(9),
            Syscall::Recv         => Some(10),
            Syscall::Sendto       => Some(11),
            Syscall::Recvfrom     => Some(12),
            Syscall::Shutdown     => Some(13),
            Syscall::Setsockopt   => Some(14),
            Syscall::Getsockopt   => Some(15),
            Syscall::Sendmsg      => Some(16),
            Syscall::Recvmsg      => Some(17),
            Syscall::Accept4      => Some(18),
            Syscall::Recvmmsg     => Some(19),
            Syscall::Sendmmsg     => Some(20),
            _ => None,
        }
    }

    /// Executable version of [`Syscall::to_ipc_arg`].
    pub(super) fn ipc_arg(&self) -> (res: Option<u64>)
        ensures res == self.to_ipc_arg()
    {
        match self {
            Syscall::Semop        => Some(1),
            Syscall::Semget       => Some(2),
            Syscall::Semctl       => Some(3),
            Syscall::Semtimedop   => Some(4),
            Syscall::Msgsnd       => Some(11),
            Syscall::Msgrcv       => Some(12),
            Syscall::Msgget       => Some(13),
            Syscall::Msgctl       => Some(14),
            Syscall::Shmat        => Some(21),
            Syscall::Shmdt        => Some(22),
            Syscall::Shmget       => Some(23),
            Syscall::Shmctl       => Some(24),
            _ => None,
        }
    }
}

impl Syscall {
    /// The syscall number at which `arch` reaches this syscall, as the filter's
    /// unsigned comparisons see it, if it reaches it at all.
    pub(super) open spec fn spec_bpf_nr(&self, arch: Arch) -> Option<u32> {
        match self.spec_nr(arch) {
            Some(nr) => Some(nr as u32),
            None => None,
        }
    }

    /// Executable version of [`Syscall::spec_bpf_nr`].
    #[verifier::when_used_as_spec(spec_bpf_nr)]
    pub(super) fn bpf_nr(&self, arch: Arch) -> (res: Option<u32>)
        ensures res == self.spec_bpf_nr(arch)
    {
        self.nr(arch).map(|nr: i32| -> (res: u32)
            ensures res == nr as u32
        { nr as u32 })
    }
}

} // verus!
