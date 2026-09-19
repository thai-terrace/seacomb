use vstd::prelude::*;
use super::policy::{Arch, Event};
 
verus! {

/// Every syscall libseccomp knows on x86, x86_64, x32, arm or aarch64 (`src/syscalls.csv`).
pub enum SyscallName {
    Accept, Accept4, Access, Acct, AddKey, Adjtimex, AfsSyscall, Alarm, ArchPrctl, ArmFadvise64_64,
    ArmSyncFileRange, Bdflush, Bind, Bpf, Break, Breakpoint, Brk, Cacheflush, Cachestat, Capget,
    Capset, Chdir, Chmod, Chown, Chown32, Chroot, ClockAdjtime, ClockAdjtime64, ClockGetres,
    ClockGetresTime64, ClockGettime, ClockGettime64, ClockNanosleep, ClockNanosleepTime64,
    ClockSettime, ClockSettime64, Clone, Clone3, Close, CloseRange, Connect, CopyFileRange, Creat,
    CreateModule, DeleteModule, Dup, Dup2, Dup3, EpollCreate, EpollCreate1, EpollCtl, EpollCtlOld,
    EpollPwait, EpollPwait2, EpollWait, EpollWaitOld, Eventfd, Eventfd2, Execve, Execveat, Exit,
    ExitGroup, Faccessat, Faccessat2, Fadvise64, Fadvise64_64, Fallocate, FanotifyInit,
    FanotifyMark, Fchdir, Fchmod, Fchmodat, Fchmodat2, Fchown, Fchown32, Fchownat, Fcntl, Fcntl64,
    Fdatasync, Fgetxattr, FileGetattr, FileSetattr, FinitModule, Flistxattr, Flock, Fork,
    Fremovexattr, Fsconfig, Fsetxattr, Fsmount, Fsopen, Fspick, Fstat, Fstat64, Fstatat64, Fstatfs,
    Fstatfs64, Fsync, Ftime, Ftruncate, Ftruncate64, Futex, FutexRequeue, FutexTime64, FutexWait,
    FutexWaitv, FutexWake, Futimesat, Getcpu, Getcwd, Getdents, Getdents64, Getegid, Getegid32,
    Geteuid, Geteuid32, Getgid, Getgid32, Getgroups, Getgroups32, Getitimer, GetKernelSyms,
    GetMempolicy, Getpeername, Getpgid, Getpgrp, Getpid, Getpmsg, Getppid, Getpriority, Getrandom,
    Getresgid, Getresgid32, Getresuid, Getresuid32, Getrlimit, GetRobustList, Getrusage, Getsid,
    Getsockname, Getsockopt, GetThreadArea, Gettid, Gettimeofday, GetTls, Getuid, Getuid32,
    Getxattr, Getxattrat, Gtty, Idle, InitModule, InotifyAddWatch, InotifyInit, InotifyInit1,
    InotifyRmWatch, IoCancel, Ioctl, IoDestroy, IoGetevents, Ioperm, IoPgetevents,
    IoPgeteventsTime64, Iopl, IoprioGet, IoprioSet, IoSetup, IoSubmit, IoUringEnter,
    IoUringRegister, IoUringSetup, Ipc, Kcmp, KexecFileLoad, KexecLoad, Keyctl, Kill,
    LandlockAddRule, LandlockCreateRuleset, LandlockRestrictSelf, Lchown, Lchown32, Lgetxattr,
    Link, Linkat, Listen, Listmount, Listns, Listxattr, Listxattrat, Llistxattr, _Llseek, Lock,
    LookupDcookie, Lremovexattr, Lseek, Lsetxattr, LsmGetSelfAttr, LsmListModules, LsmSetSelfAttr,
    Lstat, Lstat64, Madvise, MapShadowStack, Mbind, Membarrier, MemfdCreate, MemfdSecret,
    MigratePages, Mincore, Mkdir, Mkdirat, Mknod, Mknodat, Mlock, Mlock2, Mlockall, Mmap, Mmap2,
    ModifyLdt, Mount, MountSetattr, MoveMount, MovePages, Mprotect, Mpx, MqGetsetattr, MqNotify,
    MqOpen, MqTimedreceive, MqTimedreceiveTime64, MqTimedsend, MqTimedsendTime64, MqUnlink, Mremap,
    Mseal, Msgctl, Msgget, Msgrcv, Msgsnd, Msync, Munlock, Munlockall, Munmap, NameToHandleAt,
    Nanosleep, Newfstatat, _Newselect, Nfsservctl, Nice, Oldfstat, Oldlstat, Oldolduname, Oldstat,
    Olduname, Open, Openat, Openat2, OpenByHandleAt, OpenTree, OpenTreeAttr, Pause,
    PciconfigIobase, PciconfigRead, PciconfigWrite, PerfEventOpen, Personality, PidfdGetfd,
    PidfdOpen, PidfdSendSignal, Pipe, Pipe2, PivotRoot, PkeyAlloc, PkeyFree, PkeyMprotect, Poll,
    Ppoll, PpollTime64, Prctl, Pread64, Preadv, Preadv2, Prlimit64, ProcessMadvise,
    ProcessMrelease, ProcessVmReadv, ProcessVmWritev, Prof, Profil, Pselect6, Pselect6Time64,
    Ptrace, Putpmsg, Pwrite64, Pwritev, Pwritev2, QueryModule, Quotactl, QuotactlFd, Read,
    Readahead, Readdir, Readlink, Readlinkat, Readv, Reboot, Recv, Recvfrom, Recvmmsg,
    RecvmmsgTime64, Recvmsg, RemapFilePages, Removexattr, Removexattrat, Rename, Renameat,
    Renameat2, RequestKey, RestartSyscall, Rmdir, Rseq, RseqSliceYield, RtSigaction, RtSigpending,
    RtSigprocmask, RtSigqueueinfo, RtSigreturn, RtSigsuspend, RtSigtimedwait, RtSigtimedwaitTime64,
    RtTgsigqueueinfo, SchedGetaffinity, SchedGetattr, SchedGetparam, SchedGetPriorityMax,
    SchedGetPriorityMin, SchedGetscheduler, SchedRrGetInterval, SchedRrGetIntervalTime64,
    SchedSetaffinity, SchedSetattr, SchedSetparam, SchedSetscheduler, SchedYield, Seccomp,
    Security, Select, Semctl, Semget, Semop, Semtimedop, SemtimedopTime64, Send, Sendfile,
    Sendfile64, Sendmmsg, Sendmsg, Sendto, Setdomainname, Setfsgid, Setfsgid32, Setfsuid,
    Setfsuid32, Setgid, Setgid32, Setgroups, Setgroups32, Sethostname, Setitimer, SetMempolicy,
    SetMempolicyHomeNode, Setns, Setpgid, Setpriority, Setregid, Setregid32, Setresgid,
    Setresgid32, Setresuid, Setresuid32, Setreuid, Setreuid32, Setrlimit, SetRobustList, Setsid,
    Setsockopt, SetThreadArea, SetTidAddress, Settimeofday, SetTls, Setuid, Setuid32, Setxattr,
    Setxattrat, Sgetmask, Shmat, Shmctl, Shmdt, Shmget, Shutdown, Sigaction, Sigaltstack, Signal,
    Signalfd, Signalfd4, Sigpending, Sigprocmask, Sigreturn, Sigsuspend, Socket, Socketcall,
    Socketpair, Splice, Ssetmask, Stat, Stat64, Statfs, Statfs64, Statmount, Statx, Stime, Stty,
    Swapoff, Swapon, Symlink, Symlinkat, Sync, SyncFileRange, Syncfs, _Sysctl, Sysfs, Sysinfo,
    Syslog, Tee, Tgkill, Time, TimerCreate, TimerDelete, TimerfdCreate, TimerfdGettime,
    TimerfdGettime64, TimerfdSettime, TimerfdSettime64, TimerGetoverrun, TimerGettime,
    TimerGettime64, TimerSettime, TimerSettime64, Times, Tkill, Truncate, Truncate64, Tuxcall,
    Ugetrlimit, Ulimit, Umask, Umount, Umount2, Uname, Unlink, Unlinkat, Unshare, Uprobe,
    Uretprobe, Uselib, Userfaultfd, Usr26, Usr32, Ustat, Utime, Utimensat, UtimensatTime64, Utimes,
    Vfork, Vhangup, Vm86, Vm86old, Vmsplice, Vserver, Wait4, Waitid, Waitpid, Write, Writev,
}

impl SyscallName {
    /// `SYS_*` from `linux/net.h`: the call number under which x86 reaches this syscall through `socketcall`.
    pub open spec fn as_socketcall_arg(self) -> Option<u64> {
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
 
    /// `linux/ipc.h`: the call number under which x86 reaches this syscall through `ipc`.
    pub open spec fn as_ipc_arg(self) -> Option<u64> {
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

/// Results of matching a syscall name against an event.
pub enum SyscallMatch {
    Exact,
    /// Matches a `socketcall` or `ipc` call.
    Mux,
    None,
}

impl Event {
    /// Whether the syscall name matches the event and if it is an exact match or a multiplexed match.
    /// TODO: Actually define this.
    pub uninterp spec fn matches_syscall(self, arch: Arch, name: SyscallName) -> SyscallMatch;
}

} // verus!
