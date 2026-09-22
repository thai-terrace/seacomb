use vstd::prelude::*;
 
verus! {

/// A helper macro to define the `Syscall` enum and its `Syscall::nr` function.
macro_rules! syscalls {
    (
        $(#[$meta:meta])*
        $vis:vis enum $name:ident {
            $(
                $( #[nr($arch:path, $nr:expr)] )*
                $variant:ident
            ),* $(,)?
        }
    ) => {
        verus! {
            $(#[$meta])*
            $vis enum $name {
                $( $variant, )*
            }

            impl $name {
                #[allow(unreachable_patterns)]
                #[verifier::opaque]
                pub open spec fn spec_nr(&self, arch: super::policy::Arch) -> Option<i32> {
                    use super::policy::*;
                    match self {
                        $(
                            $name::$variant => match arch {
                                $( $arch => Some(($nr) as i32), )*
                                _ => None,
                            },
                        )*
                    }
                }

                /// Executable version of [`Self::spec_nr`].
                #[allow(unreachable_patterns)]
                #[verifier::when_used_as_spec(spec_nr)]
                pub fn nr(&self, arch: super::policy::Arch) -> (res: Option<i32>)
                    ensures res == self.spec_nr(arch)
                {
                    use super::policy::*;
                    reveal($name::spec_nr);
                    match self {
                        $(
                            $name::$variant => match arch {
                                $( $arch => Some(($nr) as i32), )*
                                _ => None,
                            },
                        )*
                    }
                }
            }
        }
    };
}

syscalls! {
    /// Linux syscall identifiers.
    ///
    /// Extracted from:
    /// - [x86 table](https://github.com/torvalds/linux/blob/v6.17/arch/x86/entry/syscalls/syscall_32.tbl)
    /// - [x86_64 table](https://github.com/torvalds/linux/blob/v6.17/arch/x86/entry/syscalls/syscall_64.tbl)
    /// - [ARM table](https://github.com/torvalds/linux/blob/v6.17/arch/arm/tools/syscall.tbl)
    /// - [AArch64 table](https://github.com/torvalds/linux/blob/v6.17/scripts/syscall.tbl)
    pub enum Syscall {
        #[nr(Arch::X86_64, 43)]
        #[nr(Arch::Arm, 285)]
        #[nr(Arch::Aarch64, 202)]
        Accept,
        #[nr(Arch::X86, 364)]
        #[nr(Arch::X86_64, 288)]
        #[nr(Arch::Arm, 366)]
        #[nr(Arch::Aarch64, 242)]
        Accept4,
        #[nr(Arch::X86, 33)]
        #[nr(Arch::X86_64, 21)]
        #[nr(Arch::Arm, 33)]
        Access,
        #[nr(Arch::X86, 51)]
        #[nr(Arch::X86_64, 163)]
        #[nr(Arch::Arm, 51)]
        #[nr(Arch::Aarch64, 89)]
        Acct,
        #[nr(Arch::X86, 286)]
        #[nr(Arch::X86_64, 248)]
        #[nr(Arch::Arm, 309)]
        #[nr(Arch::Aarch64, 217)]
        AddKey,
        #[nr(Arch::X86, 124)]
        #[nr(Arch::X86_64, 159)]
        #[nr(Arch::Arm, 124)]
        #[nr(Arch::Aarch64, 171)]
        Adjtimex,
        #[nr(Arch::X86, 137)]
        #[nr(Arch::X86_64, 183)]
        AfsSyscall,
        #[nr(Arch::X86, 27)]
        #[nr(Arch::X86_64, 37)]
        Alarm,
        #[nr(Arch::X86, 384)]
        #[nr(Arch::X86_64, 158)]
        ArchPrctl,
        #[nr(Arch::Arm, 270)]
        ArmFadvise64_64,
        #[nr(Arch::Arm, 341)]
        ArmSyncFileRange,
        #[nr(Arch::X86, 134)]
        #[nr(Arch::Arm, 134)]
        Bdflush,
        #[nr(Arch::X86, 361)]
        #[nr(Arch::X86_64, 49)]
        #[nr(Arch::Arm, 282)]
        #[nr(Arch::Aarch64, 200)]
        Bind,
        #[nr(Arch::X86, 357)]
        #[nr(Arch::X86_64, 321)]
        #[nr(Arch::Arm, 386)]
        #[nr(Arch::Aarch64, 280)]
        Bpf,
        #[nr(Arch::X86, 17)]
        Break,
        #[nr(Arch::Arm, 983041)]
        Breakpoint,
        #[nr(Arch::X86, 45)]
        #[nr(Arch::X86_64, 12)]
        #[nr(Arch::Arm, 45)]
        #[nr(Arch::Aarch64, 214)]
        Brk,
        #[nr(Arch::Arm, 983042)]
        Cacheflush,
        #[nr(Arch::X86, 451)]
        #[nr(Arch::X86_64, 451)]
        #[nr(Arch::Arm, 451)]
        #[nr(Arch::Aarch64, 451)]
        Cachestat,
        #[nr(Arch::X86, 184)]
        #[nr(Arch::X86_64, 125)]
        #[nr(Arch::Arm, 184)]
        #[nr(Arch::Aarch64, 90)]
        Capget,
        #[nr(Arch::X86, 185)]
        #[nr(Arch::X86_64, 126)]
        #[nr(Arch::Arm, 185)]
        #[nr(Arch::Aarch64, 91)]
        Capset,
        #[nr(Arch::X86, 12)]
        #[nr(Arch::X86_64, 80)]
        #[nr(Arch::Arm, 12)]
        #[nr(Arch::Aarch64, 49)]
        Chdir,
        #[nr(Arch::X86, 15)]
        #[nr(Arch::X86_64, 90)]
        #[nr(Arch::Arm, 15)]
        Chmod,
        #[nr(Arch::X86, 182)]
        #[nr(Arch::X86_64, 92)]
        #[nr(Arch::Arm, 182)]
        Chown,
        #[nr(Arch::X86, 212)]
        #[nr(Arch::Arm, 212)]
        Chown32,
        #[nr(Arch::X86, 61)]
        #[nr(Arch::X86_64, 161)]
        #[nr(Arch::Arm, 61)]
        #[nr(Arch::Aarch64, 51)]
        Chroot,
        #[nr(Arch::X86, 343)]
        #[nr(Arch::X86_64, 305)]
        #[nr(Arch::Arm, 372)]
        #[nr(Arch::Aarch64, 266)]
        ClockAdjtime,
        #[nr(Arch::X86, 405)]
        #[nr(Arch::Arm, 405)]
        ClockAdjtime64,
        #[nr(Arch::X86, 266)]
        #[nr(Arch::X86_64, 229)]
        #[nr(Arch::Arm, 264)]
        #[nr(Arch::Aarch64, 114)]
        ClockGetres,
        #[nr(Arch::X86, 406)]
        #[nr(Arch::Arm, 406)]
        ClockGetresTime64,
        #[nr(Arch::X86, 265)]
        #[nr(Arch::X86_64, 228)]
        #[nr(Arch::Arm, 263)]
        #[nr(Arch::Aarch64, 113)]
        ClockGettime,
        #[nr(Arch::X86, 403)]
        #[nr(Arch::Arm, 403)]
        ClockGettime64,
        #[nr(Arch::X86, 267)]
        #[nr(Arch::X86_64, 230)]
        #[nr(Arch::Arm, 265)]
        #[nr(Arch::Aarch64, 115)]
        ClockNanosleep,
        #[nr(Arch::X86, 407)]
        #[nr(Arch::Arm, 407)]
        ClockNanosleepTime64,
        #[nr(Arch::X86, 264)]
        #[nr(Arch::X86_64, 227)]
        #[nr(Arch::Arm, 262)]
        #[nr(Arch::Aarch64, 112)]
        ClockSettime,
        #[nr(Arch::X86, 404)]
        #[nr(Arch::Arm, 404)]
        ClockSettime64,
        #[nr(Arch::X86, 120)]
        #[nr(Arch::X86_64, 56)]
        #[nr(Arch::Arm, 120)]
        #[nr(Arch::Aarch64, 220)]
        Clone,
        #[nr(Arch::X86, 435)]
        #[nr(Arch::X86_64, 435)]
        #[nr(Arch::Arm, 435)]
        #[nr(Arch::Aarch64, 435)]
        Clone3,
        #[nr(Arch::X86, 6)]
        #[nr(Arch::X86_64, 3)]
        #[nr(Arch::Arm, 6)]
        #[nr(Arch::Aarch64, 57)]
        Close,
        #[nr(Arch::X86, 436)]
        #[nr(Arch::X86_64, 436)]
        #[nr(Arch::Arm, 436)]
        #[nr(Arch::Aarch64, 436)]
        CloseRange,
        #[nr(Arch::X86, 362)]
        #[nr(Arch::X86_64, 42)]
        #[nr(Arch::Arm, 283)]
        #[nr(Arch::Aarch64, 203)]
        Connect,
        #[nr(Arch::X86, 377)]
        #[nr(Arch::X86_64, 326)]
        #[nr(Arch::Arm, 391)]
        #[nr(Arch::Aarch64, 285)]
        CopyFileRange,
        #[nr(Arch::X86, 8)]
        #[nr(Arch::X86_64, 85)]
        #[nr(Arch::Arm, 8)]
        Creat,
        #[nr(Arch::X86, 127)]
        #[nr(Arch::X86_64, 174)]
        CreateModule,
        #[nr(Arch::X86, 129)]
        #[nr(Arch::X86_64, 176)]
        #[nr(Arch::Arm, 129)]
        #[nr(Arch::Aarch64, 106)]
        DeleteModule,
        #[nr(Arch::X86, 41)]
        #[nr(Arch::X86_64, 32)]
        #[nr(Arch::Arm, 41)]
        #[nr(Arch::Aarch64, 23)]
        Dup,
        #[nr(Arch::X86, 63)]
        #[nr(Arch::X86_64, 33)]
        #[nr(Arch::Arm, 63)]
        Dup2,
        #[nr(Arch::X86, 330)]
        #[nr(Arch::X86_64, 292)]
        #[nr(Arch::Arm, 358)]
        #[nr(Arch::Aarch64, 24)]
        Dup3,
        #[nr(Arch::X86, 254)]
        #[nr(Arch::X86_64, 213)]
        #[nr(Arch::Arm, 250)]
        EpollCreate,
        #[nr(Arch::X86, 329)]
        #[nr(Arch::X86_64, 291)]
        #[nr(Arch::Arm, 357)]
        #[nr(Arch::Aarch64, 20)]
        EpollCreate1,
        #[nr(Arch::X86, 255)]
        #[nr(Arch::X86_64, 233)]
        #[nr(Arch::Arm, 251)]
        #[nr(Arch::Aarch64, 21)]
        EpollCtl,
        #[nr(Arch::X86_64, 214)]
        EpollCtlOld,
        #[nr(Arch::X86, 319)]
        #[nr(Arch::X86_64, 281)]
        #[nr(Arch::Arm, 346)]
        #[nr(Arch::Aarch64, 22)]
        EpollPwait,
        #[nr(Arch::X86, 441)]
        #[nr(Arch::X86_64, 441)]
        #[nr(Arch::Arm, 441)]
        #[nr(Arch::Aarch64, 441)]
        EpollPwait2,
        #[nr(Arch::X86, 256)]
        #[nr(Arch::X86_64, 232)]
        #[nr(Arch::Arm, 252)]
        EpollWait,
        #[nr(Arch::X86_64, 215)]
        EpollWaitOld,
        #[nr(Arch::X86, 323)]
        #[nr(Arch::X86_64, 284)]
        #[nr(Arch::Arm, 351)]
        Eventfd,
        #[nr(Arch::X86, 328)]
        #[nr(Arch::X86_64, 290)]
        #[nr(Arch::Arm, 356)]
        #[nr(Arch::Aarch64, 19)]
        Eventfd2,
        #[nr(Arch::X86, 11)]
        #[nr(Arch::X86_64, 59)]
        #[nr(Arch::Arm, 11)]
        #[nr(Arch::Aarch64, 221)]
        Execve,
        #[nr(Arch::X86, 358)]
        #[nr(Arch::X86_64, 322)]
        #[nr(Arch::Arm, 387)]
        #[nr(Arch::Aarch64, 281)]
        Execveat,
        #[nr(Arch::X86, 1)]
        #[nr(Arch::X86_64, 60)]
        #[nr(Arch::Arm, 1)]
        #[nr(Arch::Aarch64, 93)]
        Exit,
        #[nr(Arch::X86, 252)]
        #[nr(Arch::X86_64, 231)]
        #[nr(Arch::Arm, 248)]
        #[nr(Arch::Aarch64, 94)]
        ExitGroup,
        #[nr(Arch::X86, 307)]
        #[nr(Arch::X86_64, 269)]
        #[nr(Arch::Arm, 334)]
        #[nr(Arch::Aarch64, 48)]
        Faccessat,
        #[nr(Arch::X86, 439)]
        #[nr(Arch::X86_64, 439)]
        #[nr(Arch::Arm, 439)]
        #[nr(Arch::Aarch64, 439)]
        Faccessat2,
        #[nr(Arch::X86, 250)]
        #[nr(Arch::X86_64, 221)]
        #[nr(Arch::Aarch64, 223)]
        Fadvise64,
        #[nr(Arch::X86, 272)]
        Fadvise64_64,
        #[nr(Arch::X86, 324)]
        #[nr(Arch::X86_64, 285)]
        #[nr(Arch::Arm, 352)]
        #[nr(Arch::Aarch64, 47)]
        Fallocate,
        #[nr(Arch::X86, 338)]
        #[nr(Arch::X86_64, 300)]
        #[nr(Arch::Arm, 367)]
        #[nr(Arch::Aarch64, 262)]
        FanotifyInit,
        #[nr(Arch::X86, 339)]
        #[nr(Arch::X86_64, 301)]
        #[nr(Arch::Arm, 368)]
        #[nr(Arch::Aarch64, 263)]
        FanotifyMark,
        #[nr(Arch::X86, 133)]
        #[nr(Arch::X86_64, 81)]
        #[nr(Arch::Arm, 133)]
        #[nr(Arch::Aarch64, 50)]
        Fchdir,
        #[nr(Arch::X86, 94)]
        #[nr(Arch::X86_64, 91)]
        #[nr(Arch::Arm, 94)]
        #[nr(Arch::Aarch64, 52)]
        Fchmod,
        #[nr(Arch::X86, 306)]
        #[nr(Arch::X86_64, 268)]
        #[nr(Arch::Arm, 333)]
        #[nr(Arch::Aarch64, 53)]
        Fchmodat,
        #[nr(Arch::X86, 452)]
        #[nr(Arch::X86_64, 452)]
        #[nr(Arch::Arm, 452)]
        #[nr(Arch::Aarch64, 452)]
        Fchmodat2,
        #[nr(Arch::X86, 95)]
        #[nr(Arch::X86_64, 93)]
        #[nr(Arch::Arm, 95)]
        #[nr(Arch::Aarch64, 55)]
        Fchown,
        #[nr(Arch::X86, 207)]
        #[nr(Arch::Arm, 207)]
        Fchown32,
        #[nr(Arch::X86, 298)]
        #[nr(Arch::X86_64, 260)]
        #[nr(Arch::Arm, 325)]
        #[nr(Arch::Aarch64, 54)]
        Fchownat,
        #[nr(Arch::X86, 55)]
        #[nr(Arch::X86_64, 72)]
        #[nr(Arch::Arm, 55)]
        #[nr(Arch::Aarch64, 25)]
        Fcntl,
        #[nr(Arch::X86, 221)]
        #[nr(Arch::Arm, 221)]
        Fcntl64,
        #[nr(Arch::X86, 148)]
        #[nr(Arch::X86_64, 75)]
        #[nr(Arch::Arm, 148)]
        #[nr(Arch::Aarch64, 83)]
        Fdatasync,
        #[nr(Arch::X86, 231)]
        #[nr(Arch::X86_64, 193)]
        #[nr(Arch::Arm, 231)]
        #[nr(Arch::Aarch64, 10)]
        Fgetxattr,
        #[nr(Arch::X86, 468)]
        #[nr(Arch::X86_64, 468)]
        #[nr(Arch::Arm, 468)]
        #[nr(Arch::Aarch64, 468)]
        FileGetattr,
        #[nr(Arch::X86, 469)]
        #[nr(Arch::X86_64, 469)]
        #[nr(Arch::Arm, 469)]
        #[nr(Arch::Aarch64, 469)]
        FileSetattr,
        #[nr(Arch::X86, 350)]
        #[nr(Arch::X86_64, 313)]
        #[nr(Arch::Arm, 379)]
        #[nr(Arch::Aarch64, 273)]
        FinitModule,
        #[nr(Arch::X86, 234)]
        #[nr(Arch::X86_64, 196)]
        #[nr(Arch::Arm, 234)]
        #[nr(Arch::Aarch64, 13)]
        Flistxattr,
        #[nr(Arch::X86, 143)]
        #[nr(Arch::X86_64, 73)]
        #[nr(Arch::Arm, 143)]
        #[nr(Arch::Aarch64, 32)]
        Flock,
        #[nr(Arch::X86, 2)]
        #[nr(Arch::X86_64, 57)]
        #[nr(Arch::Arm, 2)]
        Fork,
        #[nr(Arch::X86, 237)]
        #[nr(Arch::X86_64, 199)]
        #[nr(Arch::Arm, 237)]
        #[nr(Arch::Aarch64, 16)]
        Fremovexattr,
        #[nr(Arch::X86, 431)]
        #[nr(Arch::X86_64, 431)]
        #[nr(Arch::Arm, 431)]
        #[nr(Arch::Aarch64, 431)]
        Fsconfig,
        #[nr(Arch::X86, 228)]
        #[nr(Arch::X86_64, 190)]
        #[nr(Arch::Arm, 228)]
        #[nr(Arch::Aarch64, 7)]
        Fsetxattr,
        #[nr(Arch::X86, 432)]
        #[nr(Arch::X86_64, 432)]
        #[nr(Arch::Arm, 432)]
        #[nr(Arch::Aarch64, 432)]
        Fsmount,
        #[nr(Arch::X86, 430)]
        #[nr(Arch::X86_64, 430)]
        #[nr(Arch::Arm, 430)]
        #[nr(Arch::Aarch64, 430)]
        Fsopen,
        #[nr(Arch::X86, 433)]
        #[nr(Arch::X86_64, 433)]
        #[nr(Arch::Arm, 433)]
        #[nr(Arch::Aarch64, 433)]
        Fspick,
        #[nr(Arch::X86, 108)]
        #[nr(Arch::X86_64, 5)]
        #[nr(Arch::Arm, 108)]
        #[nr(Arch::Aarch64, 80)]
        Fstat,
        #[nr(Arch::X86, 197)]
        #[nr(Arch::Arm, 197)]
        Fstat64,
        #[nr(Arch::X86, 300)]
        #[nr(Arch::Arm, 327)]
        Fstatat64,
        #[nr(Arch::X86, 100)]
        #[nr(Arch::X86_64, 138)]
        #[nr(Arch::Arm, 100)]
        #[nr(Arch::Aarch64, 44)]
        Fstatfs,
        #[nr(Arch::X86, 269)]
        #[nr(Arch::Arm, 267)]
        Fstatfs64,
        #[nr(Arch::X86, 118)]
        #[nr(Arch::X86_64, 74)]
        #[nr(Arch::Arm, 118)]
        #[nr(Arch::Aarch64, 82)]
        Fsync,
        #[nr(Arch::X86, 35)]
        Ftime,
        #[nr(Arch::X86, 93)]
        #[nr(Arch::X86_64, 77)]
        #[nr(Arch::Arm, 93)]
        #[nr(Arch::Aarch64, 46)]
        Ftruncate,
        #[nr(Arch::X86, 194)]
        #[nr(Arch::Arm, 194)]
        Ftruncate64,
        #[nr(Arch::X86, 240)]
        #[nr(Arch::X86_64, 202)]
        #[nr(Arch::Arm, 240)]
        #[nr(Arch::Aarch64, 98)]
        Futex,
        #[nr(Arch::X86, 456)]
        #[nr(Arch::X86_64, 456)]
        #[nr(Arch::Arm, 456)]
        #[nr(Arch::Aarch64, 456)]
        FutexRequeue,
        #[nr(Arch::X86, 422)]
        #[nr(Arch::Arm, 422)]
        FutexTime64,
        #[nr(Arch::X86, 455)]
        #[nr(Arch::X86_64, 455)]
        #[nr(Arch::Arm, 455)]
        #[nr(Arch::Aarch64, 455)]
        FutexWait,
        #[nr(Arch::X86, 449)]
        #[nr(Arch::X86_64, 449)]
        #[nr(Arch::Arm, 449)]
        #[nr(Arch::Aarch64, 449)]
        FutexWaitv,
        #[nr(Arch::X86, 454)]
        #[nr(Arch::X86_64, 454)]
        #[nr(Arch::Arm, 454)]
        #[nr(Arch::Aarch64, 454)]
        FutexWake,
        #[nr(Arch::X86, 299)]
        #[nr(Arch::X86_64, 261)]
        #[nr(Arch::Arm, 326)]
        Futimesat,
        #[nr(Arch::X86, 318)]
        #[nr(Arch::X86_64, 309)]
        #[nr(Arch::Arm, 345)]
        #[nr(Arch::Aarch64, 168)]
        Getcpu,
        #[nr(Arch::X86, 183)]
        #[nr(Arch::X86_64, 79)]
        #[nr(Arch::Arm, 183)]
        #[nr(Arch::Aarch64, 17)]
        Getcwd,
        #[nr(Arch::X86, 141)]
        #[nr(Arch::X86_64, 78)]
        #[nr(Arch::Arm, 141)]
        Getdents,
        #[nr(Arch::X86, 220)]
        #[nr(Arch::X86_64, 217)]
        #[nr(Arch::Arm, 217)]
        #[nr(Arch::Aarch64, 61)]
        Getdents64,
        #[nr(Arch::X86, 50)]
        #[nr(Arch::X86_64, 108)]
        #[nr(Arch::Arm, 50)]
        #[nr(Arch::Aarch64, 177)]
        Getegid,
        #[nr(Arch::X86, 202)]
        #[nr(Arch::Arm, 202)]
        Getegid32,
        #[nr(Arch::X86, 49)]
        #[nr(Arch::X86_64, 107)]
        #[nr(Arch::Arm, 49)]
        #[nr(Arch::Aarch64, 175)]
        Geteuid,
        #[nr(Arch::X86, 201)]
        #[nr(Arch::Arm, 201)]
        Geteuid32,
        #[nr(Arch::X86, 47)]
        #[nr(Arch::X86_64, 104)]
        #[nr(Arch::Arm, 47)]
        #[nr(Arch::Aarch64, 176)]
        Getgid,
        #[nr(Arch::X86, 200)]
        #[nr(Arch::Arm, 200)]
        Getgid32,
        #[nr(Arch::X86, 80)]
        #[nr(Arch::X86_64, 115)]
        #[nr(Arch::Arm, 80)]
        #[nr(Arch::Aarch64, 158)]
        Getgroups,
        #[nr(Arch::X86, 205)]
        #[nr(Arch::Arm, 205)]
        Getgroups32,
        #[nr(Arch::X86, 105)]
        #[nr(Arch::X86_64, 36)]
        #[nr(Arch::Arm, 105)]
        #[nr(Arch::Aarch64, 102)]
        Getitimer,
        #[nr(Arch::X86, 130)]
        #[nr(Arch::X86_64, 177)]
        GetKernelSyms,
        #[nr(Arch::X86, 275)]
        #[nr(Arch::X86_64, 239)]
        #[nr(Arch::Arm, 320)]
        #[nr(Arch::Aarch64, 236)]
        GetMempolicy,
        #[nr(Arch::X86, 368)]
        #[nr(Arch::X86_64, 52)]
        #[nr(Arch::Arm, 287)]
        #[nr(Arch::Aarch64, 205)]
        Getpeername,
        #[nr(Arch::X86, 132)]
        #[nr(Arch::X86_64, 121)]
        #[nr(Arch::Arm, 132)]
        #[nr(Arch::Aarch64, 155)]
        Getpgid,
        #[nr(Arch::X86, 65)]
        #[nr(Arch::X86_64, 111)]
        #[nr(Arch::Arm, 65)]
        Getpgrp,
        #[nr(Arch::X86, 20)]
        #[nr(Arch::X86_64, 39)]
        #[nr(Arch::Arm, 20)]
        #[nr(Arch::Aarch64, 172)]
        Getpid,
        #[nr(Arch::X86, 188)]
        #[nr(Arch::X86_64, 181)]
        Getpmsg,
        #[nr(Arch::X86, 64)]
        #[nr(Arch::X86_64, 110)]
        #[nr(Arch::Arm, 64)]
        #[nr(Arch::Aarch64, 173)]
        Getppid,
        #[nr(Arch::X86, 96)]
        #[nr(Arch::X86_64, 140)]
        #[nr(Arch::Arm, 96)]
        #[nr(Arch::Aarch64, 141)]
        Getpriority,
        #[nr(Arch::X86, 355)]
        #[nr(Arch::X86_64, 318)]
        #[nr(Arch::Arm, 384)]
        #[nr(Arch::Aarch64, 278)]
        Getrandom,
        #[nr(Arch::X86, 171)]
        #[nr(Arch::X86_64, 120)]
        #[nr(Arch::Arm, 171)]
        #[nr(Arch::Aarch64, 150)]
        Getresgid,
        #[nr(Arch::X86, 211)]
        #[nr(Arch::Arm, 211)]
        Getresgid32,
        #[nr(Arch::X86, 165)]
        #[nr(Arch::X86_64, 118)]
        #[nr(Arch::Arm, 165)]
        #[nr(Arch::Aarch64, 148)]
        Getresuid,
        #[nr(Arch::X86, 209)]
        #[nr(Arch::Arm, 209)]
        Getresuid32,
        #[nr(Arch::X86, 76)]
        #[nr(Arch::X86_64, 97)]
        #[nr(Arch::Aarch64, 163)]
        Getrlimit,
        #[nr(Arch::X86, 312)]
        #[nr(Arch::X86_64, 274)]
        #[nr(Arch::Arm, 339)]
        #[nr(Arch::Aarch64, 100)]
        GetRobustList,
        #[nr(Arch::X86, 77)]
        #[nr(Arch::X86_64, 98)]
        #[nr(Arch::Arm, 77)]
        #[nr(Arch::Aarch64, 165)]
        Getrusage,
        #[nr(Arch::X86, 147)]
        #[nr(Arch::X86_64, 124)]
        #[nr(Arch::Arm, 147)]
        #[nr(Arch::Aarch64, 156)]
        Getsid,
        #[nr(Arch::X86, 367)]
        #[nr(Arch::X86_64, 51)]
        #[nr(Arch::Arm, 286)]
        #[nr(Arch::Aarch64, 204)]
        Getsockname,
        #[nr(Arch::X86, 365)]
        #[nr(Arch::X86_64, 55)]
        #[nr(Arch::Arm, 295)]
        #[nr(Arch::Aarch64, 209)]
        Getsockopt,
        #[nr(Arch::X86, 244)]
        #[nr(Arch::X86_64, 211)]
        GetThreadArea,
        #[nr(Arch::X86, 224)]
        #[nr(Arch::X86_64, 186)]
        #[nr(Arch::Arm, 224)]
        #[nr(Arch::Aarch64, 178)]
        Gettid,
        #[nr(Arch::X86, 78)]
        #[nr(Arch::X86_64, 96)]
        #[nr(Arch::Arm, 78)]
        #[nr(Arch::Aarch64, 169)]
        Gettimeofday,
        #[nr(Arch::Arm, 983046)]
        GetTls,
        #[nr(Arch::X86, 24)]
        #[nr(Arch::X86_64, 102)]
        #[nr(Arch::Arm, 24)]
        #[nr(Arch::Aarch64, 174)]
        Getuid,
        #[nr(Arch::X86, 199)]
        #[nr(Arch::Arm, 199)]
        Getuid32,
        #[nr(Arch::X86, 229)]
        #[nr(Arch::X86_64, 191)]
        #[nr(Arch::Arm, 229)]
        #[nr(Arch::Aarch64, 8)]
        Getxattr,
        #[nr(Arch::X86, 464)]
        #[nr(Arch::X86_64, 464)]
        #[nr(Arch::Arm, 464)]
        #[nr(Arch::Aarch64, 464)]
        Getxattrat,
        #[nr(Arch::X86, 32)]
        Gtty,
        #[nr(Arch::X86, 112)]
        Idle,
        #[nr(Arch::X86, 128)]
        #[nr(Arch::X86_64, 175)]
        #[nr(Arch::Arm, 128)]
        #[nr(Arch::Aarch64, 105)]
        InitModule,
        #[nr(Arch::X86, 292)]
        #[nr(Arch::X86_64, 254)]
        #[nr(Arch::Arm, 317)]
        #[nr(Arch::Aarch64, 27)]
        InotifyAddWatch,
        #[nr(Arch::X86, 291)]
        #[nr(Arch::X86_64, 253)]
        #[nr(Arch::Arm, 316)]
        InotifyInit,
        #[nr(Arch::X86, 332)]
        #[nr(Arch::X86_64, 294)]
        #[nr(Arch::Arm, 360)]
        #[nr(Arch::Aarch64, 26)]
        InotifyInit1,
        #[nr(Arch::X86, 293)]
        #[nr(Arch::X86_64, 255)]
        #[nr(Arch::Arm, 318)]
        #[nr(Arch::Aarch64, 28)]
        InotifyRmWatch,
        #[nr(Arch::X86, 249)]
        #[nr(Arch::X86_64, 210)]
        #[nr(Arch::Arm, 247)]
        #[nr(Arch::Aarch64, 3)]
        IoCancel,
        #[nr(Arch::X86, 54)]
        #[nr(Arch::X86_64, 16)]
        #[nr(Arch::Arm, 54)]
        #[nr(Arch::Aarch64, 29)]
        Ioctl,
        #[nr(Arch::X86, 246)]
        #[nr(Arch::X86_64, 207)]
        #[nr(Arch::Arm, 244)]
        #[nr(Arch::Aarch64, 1)]
        IoDestroy,
        #[nr(Arch::X86, 247)]
        #[nr(Arch::X86_64, 208)]
        #[nr(Arch::Arm, 245)]
        #[nr(Arch::Aarch64, 4)]
        IoGetevents,
        #[nr(Arch::X86, 101)]
        #[nr(Arch::X86_64, 173)]
        Ioperm,
        #[nr(Arch::X86, 385)]
        #[nr(Arch::X86_64, 333)]
        #[nr(Arch::Arm, 399)]
        #[nr(Arch::Aarch64, 292)]
        IoPgetevents,
        #[nr(Arch::X86, 416)]
        #[nr(Arch::Arm, 416)]
        IoPgeteventsTime64,
        #[nr(Arch::X86, 110)]
        #[nr(Arch::X86_64, 172)]
        Iopl,
        #[nr(Arch::X86, 290)]
        #[nr(Arch::X86_64, 252)]
        #[nr(Arch::Arm, 315)]
        #[nr(Arch::Aarch64, 31)]
        IoprioGet,
        #[nr(Arch::X86, 289)]
        #[nr(Arch::X86_64, 251)]
        #[nr(Arch::Arm, 314)]
        #[nr(Arch::Aarch64, 30)]
        IoprioSet,
        #[nr(Arch::X86, 245)]
        #[nr(Arch::X86_64, 206)]
        #[nr(Arch::Arm, 243)]
        #[nr(Arch::Aarch64, 0)]
        IoSetup,
        #[nr(Arch::X86, 248)]
        #[nr(Arch::X86_64, 209)]
        #[nr(Arch::Arm, 246)]
        #[nr(Arch::Aarch64, 2)]
        IoSubmit,
        #[nr(Arch::X86, 426)]
        #[nr(Arch::X86_64, 426)]
        #[nr(Arch::Arm, 426)]
        #[nr(Arch::Aarch64, 426)]
        IoUringEnter,
        #[nr(Arch::X86, 427)]
        #[nr(Arch::X86_64, 427)]
        #[nr(Arch::Arm, 427)]
        #[nr(Arch::Aarch64, 427)]
        IoUringRegister,
        #[nr(Arch::X86, 425)]
        #[nr(Arch::X86_64, 425)]
        #[nr(Arch::Arm, 425)]
        #[nr(Arch::Aarch64, 425)]
        IoUringSetup,
        #[nr(Arch::X86, 117)]
        Ipc,
        #[nr(Arch::X86, 349)]
        #[nr(Arch::X86_64, 312)]
        #[nr(Arch::Arm, 378)]
        #[nr(Arch::Aarch64, 272)]
        Kcmp,
        #[nr(Arch::X86_64, 320)]
        #[nr(Arch::Arm, 401)]
        #[nr(Arch::Aarch64, 294)]
        KexecFileLoad,
        #[nr(Arch::X86, 283)]
        #[nr(Arch::X86_64, 246)]
        #[nr(Arch::Arm, 347)]
        #[nr(Arch::Aarch64, 104)]
        KexecLoad,
        #[nr(Arch::X86, 288)]
        #[nr(Arch::X86_64, 250)]
        #[nr(Arch::Arm, 311)]
        #[nr(Arch::Aarch64, 219)]
        Keyctl,
        #[nr(Arch::X86, 37)]
        #[nr(Arch::X86_64, 62)]
        #[nr(Arch::Arm, 37)]
        #[nr(Arch::Aarch64, 129)]
        Kill,
        #[nr(Arch::X86, 445)]
        #[nr(Arch::X86_64, 445)]
        #[nr(Arch::Arm, 445)]
        #[nr(Arch::Aarch64, 445)]
        LandlockAddRule,
        #[nr(Arch::X86, 444)]
        #[nr(Arch::X86_64, 444)]
        #[nr(Arch::Arm, 444)]
        #[nr(Arch::Aarch64, 444)]
        LandlockCreateRuleset,
        #[nr(Arch::X86, 446)]
        #[nr(Arch::X86_64, 446)]
        #[nr(Arch::Arm, 446)]
        #[nr(Arch::Aarch64, 446)]
        LandlockRestrictSelf,
        #[nr(Arch::X86, 16)]
        #[nr(Arch::X86_64, 94)]
        #[nr(Arch::Arm, 16)]
        Lchown,
        #[nr(Arch::X86, 198)]
        #[nr(Arch::Arm, 198)]
        Lchown32,
        #[nr(Arch::X86, 230)]
        #[nr(Arch::X86_64, 192)]
        #[nr(Arch::Arm, 230)]
        #[nr(Arch::Aarch64, 9)]
        Lgetxattr,
        #[nr(Arch::X86, 9)]
        #[nr(Arch::X86_64, 86)]
        #[nr(Arch::Arm, 9)]
        Link,
        #[nr(Arch::X86, 303)]
        #[nr(Arch::X86_64, 265)]
        #[nr(Arch::Arm, 330)]
        #[nr(Arch::Aarch64, 37)]
        Linkat,
        #[nr(Arch::X86, 363)]
        #[nr(Arch::X86_64, 50)]
        #[nr(Arch::Arm, 284)]
        #[nr(Arch::Aarch64, 201)]
        Listen,
        #[nr(Arch::X86, 458)]
        #[nr(Arch::X86_64, 458)]
        #[nr(Arch::Arm, 458)]
        #[nr(Arch::Aarch64, 458)]
        Listmount,
        #[nr(Arch::X86, 470)]
        #[nr(Arch::X86_64, 470)]
        #[nr(Arch::Arm, 470)]
        #[nr(Arch::Aarch64, 470)]
        Listns,
        #[nr(Arch::X86, 232)]
        #[nr(Arch::X86_64, 194)]
        #[nr(Arch::Arm, 232)]
        #[nr(Arch::Aarch64, 11)]
        Listxattr,
        #[nr(Arch::X86, 465)]
        #[nr(Arch::X86_64, 465)]
        #[nr(Arch::Arm, 465)]
        #[nr(Arch::Aarch64, 465)]
        Listxattrat,
        #[nr(Arch::X86, 233)]
        #[nr(Arch::X86_64, 195)]
        #[nr(Arch::Arm, 233)]
        #[nr(Arch::Aarch64, 12)]
        Llistxattr,
        #[nr(Arch::X86, 140)]
        #[nr(Arch::Arm, 140)]
        _Llseek,
        #[nr(Arch::X86, 53)]
        Lock,
        #[nr(Arch::X86, 253)]
        #[nr(Arch::X86_64, 212)]
        #[nr(Arch::Arm, 249)]
        #[nr(Arch::Aarch64, 18)]
        LookupDcookie,
        #[nr(Arch::X86, 236)]
        #[nr(Arch::X86_64, 198)]
        #[nr(Arch::Arm, 236)]
        #[nr(Arch::Aarch64, 15)]
        Lremovexattr,
        #[nr(Arch::X86, 19)]
        #[nr(Arch::X86_64, 8)]
        #[nr(Arch::Arm, 19)]
        #[nr(Arch::Aarch64, 62)]
        Lseek,
        #[nr(Arch::X86, 227)]
        #[nr(Arch::X86_64, 189)]
        #[nr(Arch::Arm, 227)]
        #[nr(Arch::Aarch64, 6)]
        Lsetxattr,
        #[nr(Arch::X86, 459)]
        #[nr(Arch::X86_64, 459)]
        #[nr(Arch::Arm, 459)]
        #[nr(Arch::Aarch64, 459)]
        LsmGetSelfAttr,
        #[nr(Arch::X86, 461)]
        #[nr(Arch::X86_64, 461)]
        #[nr(Arch::Arm, 461)]
        #[nr(Arch::Aarch64, 461)]
        LsmListModules,
        #[nr(Arch::X86, 460)]
        #[nr(Arch::X86_64, 460)]
        #[nr(Arch::Arm, 460)]
        #[nr(Arch::Aarch64, 460)]
        LsmSetSelfAttr,
        #[nr(Arch::X86, 107)]
        #[nr(Arch::X86_64, 6)]
        #[nr(Arch::Arm, 107)]
        Lstat,
        #[nr(Arch::X86, 196)]
        #[nr(Arch::Arm, 196)]
        Lstat64,
        #[nr(Arch::X86, 219)]
        #[nr(Arch::X86_64, 28)]
        #[nr(Arch::Arm, 220)]
        #[nr(Arch::Aarch64, 233)]
        Madvise,
        #[nr(Arch::X86, 453)]
        #[nr(Arch::X86_64, 453)]
        #[nr(Arch::Arm, 453)]
        #[nr(Arch::Aarch64, 453)]
        MapShadowStack,
        #[nr(Arch::X86, 274)]
        #[nr(Arch::X86_64, 237)]
        #[nr(Arch::Arm, 319)]
        #[nr(Arch::Aarch64, 235)]
        Mbind,
        #[nr(Arch::X86, 375)]
        #[nr(Arch::X86_64, 324)]
        #[nr(Arch::Arm, 389)]
        #[nr(Arch::Aarch64, 283)]
        Membarrier,
        #[nr(Arch::X86, 356)]
        #[nr(Arch::X86_64, 319)]
        #[nr(Arch::Arm, 385)]
        #[nr(Arch::Aarch64, 279)]
        MemfdCreate,
        #[nr(Arch::X86, 447)]
        #[nr(Arch::X86_64, 447)]
        #[nr(Arch::Aarch64, 447)]
        MemfdSecret,
        #[nr(Arch::X86, 294)]
        #[nr(Arch::X86_64, 256)]
        #[nr(Arch::Arm, 400)]
        #[nr(Arch::Aarch64, 238)]
        MigratePages,
        #[nr(Arch::X86, 218)]
        #[nr(Arch::X86_64, 27)]
        #[nr(Arch::Arm, 219)]
        #[nr(Arch::Aarch64, 232)]
        Mincore,
        #[nr(Arch::X86, 39)]
        #[nr(Arch::X86_64, 83)]
        #[nr(Arch::Arm, 39)]
        Mkdir,
        #[nr(Arch::X86, 296)]
        #[nr(Arch::X86_64, 258)]
        #[nr(Arch::Arm, 323)]
        #[nr(Arch::Aarch64, 34)]
        Mkdirat,
        #[nr(Arch::X86, 14)]
        #[nr(Arch::X86_64, 133)]
        #[nr(Arch::Arm, 14)]
        Mknod,
        #[nr(Arch::X86, 297)]
        #[nr(Arch::X86_64, 259)]
        #[nr(Arch::Arm, 324)]
        #[nr(Arch::Aarch64, 33)]
        Mknodat,
        #[nr(Arch::X86, 150)]
        #[nr(Arch::X86_64, 149)]
        #[nr(Arch::Arm, 150)]
        #[nr(Arch::Aarch64, 228)]
        Mlock,
        #[nr(Arch::X86, 376)]
        #[nr(Arch::X86_64, 325)]
        #[nr(Arch::Arm, 390)]
        #[nr(Arch::Aarch64, 284)]
        Mlock2,
        #[nr(Arch::X86, 152)]
        #[nr(Arch::X86_64, 151)]
        #[nr(Arch::Arm, 152)]
        #[nr(Arch::Aarch64, 230)]
        Mlockall,
        #[nr(Arch::X86, 90)]
        #[nr(Arch::X86_64, 9)]
        #[nr(Arch::Aarch64, 222)]
        Mmap,
        #[nr(Arch::X86, 192)]
        #[nr(Arch::Arm, 192)]
        Mmap2,
        #[nr(Arch::X86, 123)]
        #[nr(Arch::X86_64, 154)]
        ModifyLdt,
        #[nr(Arch::X86, 21)]
        #[nr(Arch::X86_64, 165)]
        #[nr(Arch::Arm, 21)]
        #[nr(Arch::Aarch64, 40)]
        Mount,
        #[nr(Arch::X86, 442)]
        #[nr(Arch::X86_64, 442)]
        #[nr(Arch::Arm, 442)]
        #[nr(Arch::Aarch64, 442)]
        MountSetattr,
        #[nr(Arch::X86, 429)]
        #[nr(Arch::X86_64, 429)]
        #[nr(Arch::Arm, 429)]
        #[nr(Arch::Aarch64, 429)]
        MoveMount,
        #[nr(Arch::X86, 317)]
        #[nr(Arch::X86_64, 279)]
        #[nr(Arch::Arm, 344)]
        #[nr(Arch::Aarch64, 239)]
        MovePages,
        #[nr(Arch::X86, 125)]
        #[nr(Arch::X86_64, 10)]
        #[nr(Arch::Arm, 125)]
        #[nr(Arch::Aarch64, 226)]
        Mprotect,
        #[nr(Arch::X86, 56)]
        Mpx,
        #[nr(Arch::X86, 282)]
        #[nr(Arch::X86_64, 245)]
        #[nr(Arch::Arm, 279)]
        #[nr(Arch::Aarch64, 185)]
        MqGetsetattr,
        #[nr(Arch::X86, 281)]
        #[nr(Arch::X86_64, 244)]
        #[nr(Arch::Arm, 278)]
        #[nr(Arch::Aarch64, 184)]
        MqNotify,
        #[nr(Arch::X86, 277)]
        #[nr(Arch::X86_64, 240)]
        #[nr(Arch::Arm, 274)]
        #[nr(Arch::Aarch64, 180)]
        MqOpen,
        #[nr(Arch::X86, 280)]
        #[nr(Arch::X86_64, 243)]
        #[nr(Arch::Arm, 277)]
        #[nr(Arch::Aarch64, 183)]
        MqTimedreceive,
        #[nr(Arch::X86, 419)]
        #[nr(Arch::Arm, 419)]
        MqTimedreceiveTime64,
        #[nr(Arch::X86, 279)]
        #[nr(Arch::X86_64, 242)]
        #[nr(Arch::Arm, 276)]
        #[nr(Arch::Aarch64, 182)]
        MqTimedsend,
        #[nr(Arch::X86, 418)]
        #[nr(Arch::Arm, 418)]
        MqTimedsendTime64,
        #[nr(Arch::X86, 278)]
        #[nr(Arch::X86_64, 241)]
        #[nr(Arch::Arm, 275)]
        #[nr(Arch::Aarch64, 181)]
        MqUnlink,
        #[nr(Arch::X86, 163)]
        #[nr(Arch::X86_64, 25)]
        #[nr(Arch::Arm, 163)]
        #[nr(Arch::Aarch64, 216)]
        Mremap,
        #[nr(Arch::X86, 462)]
        #[nr(Arch::X86_64, 462)]
        #[nr(Arch::Arm, 462)]
        #[nr(Arch::Aarch64, 462)]
        Mseal,
        #[nr(Arch::X86, 402)]
        #[nr(Arch::X86_64, 71)]
        #[nr(Arch::Arm, 304)]
        #[nr(Arch::Aarch64, 187)]
        Msgctl,
        #[nr(Arch::X86, 399)]
        #[nr(Arch::X86_64, 68)]
        #[nr(Arch::Arm, 303)]
        #[nr(Arch::Aarch64, 186)]
        Msgget,
        #[nr(Arch::X86, 401)]
        #[nr(Arch::X86_64, 70)]
        #[nr(Arch::Arm, 302)]
        #[nr(Arch::Aarch64, 188)]
        Msgrcv,
        #[nr(Arch::X86, 400)]
        #[nr(Arch::X86_64, 69)]
        #[nr(Arch::Arm, 301)]
        #[nr(Arch::Aarch64, 189)]
        Msgsnd,
        #[nr(Arch::X86, 144)]
        #[nr(Arch::X86_64, 26)]
        #[nr(Arch::Arm, 144)]
        #[nr(Arch::Aarch64, 227)]
        Msync,
        #[nr(Arch::X86, 151)]
        #[nr(Arch::X86_64, 150)]
        #[nr(Arch::Arm, 151)]
        #[nr(Arch::Aarch64, 229)]
        Munlock,
        #[nr(Arch::X86, 153)]
        #[nr(Arch::X86_64, 152)]
        #[nr(Arch::Arm, 153)]
        #[nr(Arch::Aarch64, 231)]
        Munlockall,
        #[nr(Arch::X86, 91)]
        #[nr(Arch::X86_64, 11)]
        #[nr(Arch::Arm, 91)]
        #[nr(Arch::Aarch64, 215)]
        Munmap,
        #[nr(Arch::X86, 341)]
        #[nr(Arch::X86_64, 303)]
        #[nr(Arch::Arm, 370)]
        #[nr(Arch::Aarch64, 264)]
        NameToHandleAt,
        #[nr(Arch::X86, 162)]
        #[nr(Arch::X86_64, 35)]
        #[nr(Arch::Arm, 162)]
        #[nr(Arch::Aarch64, 101)]
        Nanosleep,
        #[nr(Arch::X86_64, 262)]
        #[nr(Arch::Aarch64, 79)]
        Newfstatat,
        #[nr(Arch::X86, 142)]
        #[nr(Arch::Arm, 142)]
        _Newselect,
        #[nr(Arch::X86, 169)]
        #[nr(Arch::X86_64, 180)]
        #[nr(Arch::Arm, 169)]
        #[nr(Arch::Aarch64, 42)]
        Nfsservctl,
        #[nr(Arch::X86, 34)]
        #[nr(Arch::Arm, 34)]
        Nice,
        #[nr(Arch::X86, 28)]
        Oldfstat,
        #[nr(Arch::X86, 84)]
        Oldlstat,
        #[nr(Arch::X86, 59)]
        Oldolduname,
        #[nr(Arch::X86, 18)]
        Oldstat,
        #[nr(Arch::X86, 109)]
        Olduname,
        #[nr(Arch::X86, 5)]
        #[nr(Arch::X86_64, 2)]
        #[nr(Arch::Arm, 5)]
        Open,
        #[nr(Arch::X86, 295)]
        #[nr(Arch::X86_64, 257)]
        #[nr(Arch::Arm, 322)]
        #[nr(Arch::Aarch64, 56)]
        Openat,
        #[nr(Arch::X86, 437)]
        #[nr(Arch::X86_64, 437)]
        #[nr(Arch::Arm, 437)]
        #[nr(Arch::Aarch64, 437)]
        Openat2,
        #[nr(Arch::X86, 342)]
        #[nr(Arch::X86_64, 304)]
        #[nr(Arch::Arm, 371)]
        #[nr(Arch::Aarch64, 265)]
        OpenByHandleAt,
        #[nr(Arch::X86, 428)]
        #[nr(Arch::X86_64, 428)]
        #[nr(Arch::Arm, 428)]
        #[nr(Arch::Aarch64, 428)]
        OpenTree,
        #[nr(Arch::X86, 467)]
        #[nr(Arch::X86_64, 467)]
        #[nr(Arch::Arm, 467)]
        #[nr(Arch::Aarch64, 467)]
        OpenTreeAttr,
        #[nr(Arch::X86, 29)]
        #[nr(Arch::X86_64, 34)]
        #[nr(Arch::Arm, 29)]
        Pause,
        #[nr(Arch::Arm, 271)]
        PciconfigIobase,
        #[nr(Arch::Arm, 272)]
        PciconfigRead,
        #[nr(Arch::Arm, 273)]
        PciconfigWrite,
        #[nr(Arch::X86, 336)]
        #[nr(Arch::X86_64, 298)]
        #[nr(Arch::Arm, 364)]
        #[nr(Arch::Aarch64, 241)]
        PerfEventOpen,
        #[nr(Arch::X86, 136)]
        #[nr(Arch::X86_64, 135)]
        #[nr(Arch::Arm, 136)]
        #[nr(Arch::Aarch64, 92)]
        Personality,
        #[nr(Arch::X86, 438)]
        #[nr(Arch::X86_64, 438)]
        #[nr(Arch::Arm, 438)]
        #[nr(Arch::Aarch64, 438)]
        PidfdGetfd,
        #[nr(Arch::X86, 434)]
        #[nr(Arch::X86_64, 434)]
        #[nr(Arch::Arm, 434)]
        #[nr(Arch::Aarch64, 434)]
        PidfdOpen,
        #[nr(Arch::X86, 424)]
        #[nr(Arch::X86_64, 424)]
        #[nr(Arch::Arm, 424)]
        #[nr(Arch::Aarch64, 424)]
        PidfdSendSignal,
        #[nr(Arch::X86, 42)]
        #[nr(Arch::X86_64, 22)]
        #[nr(Arch::Arm, 42)]
        Pipe,
        #[nr(Arch::X86, 331)]
        #[nr(Arch::X86_64, 293)]
        #[nr(Arch::Arm, 359)]
        #[nr(Arch::Aarch64, 59)]
        Pipe2,
        #[nr(Arch::X86, 217)]
        #[nr(Arch::X86_64, 155)]
        #[nr(Arch::Arm, 218)]
        #[nr(Arch::Aarch64, 41)]
        PivotRoot,
        #[nr(Arch::X86, 381)]
        #[nr(Arch::X86_64, 330)]
        #[nr(Arch::Arm, 395)]
        #[nr(Arch::Aarch64, 289)]
        PkeyAlloc,
        #[nr(Arch::X86, 382)]
        #[nr(Arch::X86_64, 331)]
        #[nr(Arch::Arm, 396)]
        #[nr(Arch::Aarch64, 290)]
        PkeyFree,
        #[nr(Arch::X86, 380)]
        #[nr(Arch::X86_64, 329)]
        #[nr(Arch::Arm, 394)]
        #[nr(Arch::Aarch64, 288)]
        PkeyMprotect,
        #[nr(Arch::X86, 168)]
        #[nr(Arch::X86_64, 7)]
        #[nr(Arch::Arm, 168)]
        Poll,
        #[nr(Arch::X86, 309)]
        #[nr(Arch::X86_64, 271)]
        #[nr(Arch::Arm, 336)]
        #[nr(Arch::Aarch64, 73)]
        Ppoll,
        #[nr(Arch::X86, 414)]
        #[nr(Arch::Arm, 414)]
        PpollTime64,
        #[nr(Arch::X86, 172)]
        #[nr(Arch::X86_64, 157)]
        #[nr(Arch::Arm, 172)]
        #[nr(Arch::Aarch64, 167)]
        Prctl,
        #[nr(Arch::X86, 180)]
        #[nr(Arch::X86_64, 17)]
        #[nr(Arch::Arm, 180)]
        #[nr(Arch::Aarch64, 67)]
        Pread64,
        #[nr(Arch::X86, 333)]
        #[nr(Arch::X86_64, 295)]
        #[nr(Arch::Arm, 361)]
        #[nr(Arch::Aarch64, 69)]
        Preadv,
        #[nr(Arch::X86, 378)]
        #[nr(Arch::X86_64, 327)]
        #[nr(Arch::Arm, 392)]
        #[nr(Arch::Aarch64, 286)]
        Preadv2,
        #[nr(Arch::X86, 340)]
        #[nr(Arch::X86_64, 302)]
        #[nr(Arch::Arm, 369)]
        #[nr(Arch::Aarch64, 261)]
        Prlimit64,
        #[nr(Arch::X86, 440)]
        #[nr(Arch::X86_64, 440)]
        #[nr(Arch::Arm, 440)]
        #[nr(Arch::Aarch64, 440)]
        ProcessMadvise,
        #[nr(Arch::X86, 448)]
        #[nr(Arch::X86_64, 448)]
        #[nr(Arch::Arm, 448)]
        #[nr(Arch::Aarch64, 448)]
        ProcessMrelease,
        #[nr(Arch::X86, 347)]
        #[nr(Arch::X86_64, 310)]
        #[nr(Arch::Arm, 376)]
        #[nr(Arch::Aarch64, 270)]
        ProcessVmReadv,
        #[nr(Arch::X86, 348)]
        #[nr(Arch::X86_64, 311)]
        #[nr(Arch::Arm, 377)]
        #[nr(Arch::Aarch64, 271)]
        ProcessVmWritev,
        #[nr(Arch::X86, 44)]
        Prof,
        #[nr(Arch::X86, 98)]
        Profil,
        #[nr(Arch::X86, 308)]
        #[nr(Arch::X86_64, 270)]
        #[nr(Arch::Arm, 335)]
        #[nr(Arch::Aarch64, 72)]
        Pselect6,
        #[nr(Arch::X86, 413)]
        #[nr(Arch::Arm, 413)]
        Pselect6Time64,
        #[nr(Arch::X86, 26)]
        #[nr(Arch::X86_64, 101)]
        #[nr(Arch::Arm, 26)]
        #[nr(Arch::Aarch64, 117)]
        Ptrace,
        #[nr(Arch::X86, 189)]
        #[nr(Arch::X86_64, 182)]
        Putpmsg,
        #[nr(Arch::X86, 181)]
        #[nr(Arch::X86_64, 18)]
        #[nr(Arch::Arm, 181)]
        #[nr(Arch::Aarch64, 68)]
        Pwrite64,
        #[nr(Arch::X86, 334)]
        #[nr(Arch::X86_64, 296)]
        #[nr(Arch::Arm, 362)]
        #[nr(Arch::Aarch64, 70)]
        Pwritev,
        #[nr(Arch::X86, 379)]
        #[nr(Arch::X86_64, 328)]
        #[nr(Arch::Arm, 393)]
        #[nr(Arch::Aarch64, 287)]
        Pwritev2,
        #[nr(Arch::X86, 167)]
        #[nr(Arch::X86_64, 178)]
        QueryModule,
        #[nr(Arch::X86, 131)]
        #[nr(Arch::X86_64, 179)]
        #[nr(Arch::Arm, 131)]
        #[nr(Arch::Aarch64, 60)]
        Quotactl,
        #[nr(Arch::X86, 443)]
        #[nr(Arch::X86_64, 443)]
        #[nr(Arch::Arm, 443)]
        #[nr(Arch::Aarch64, 443)]
        QuotactlFd,
        #[nr(Arch::X86, 3)]
        #[nr(Arch::X86_64, 0)]
        #[nr(Arch::Arm, 3)]
        #[nr(Arch::Aarch64, 63)]
        Read,
        #[nr(Arch::X86, 225)]
        #[nr(Arch::X86_64, 187)]
        #[nr(Arch::Arm, 225)]
        #[nr(Arch::Aarch64, 213)]
        Readahead,
        #[nr(Arch::X86, 89)]
        Readdir,
        #[nr(Arch::X86, 85)]
        #[nr(Arch::X86_64, 89)]
        #[nr(Arch::Arm, 85)]
        Readlink,
        #[nr(Arch::X86, 305)]
        #[nr(Arch::X86_64, 267)]
        #[nr(Arch::Arm, 332)]
        #[nr(Arch::Aarch64, 78)]
        Readlinkat,
        #[nr(Arch::X86, 145)]
        #[nr(Arch::X86_64, 19)]
        #[nr(Arch::Arm, 145)]
        #[nr(Arch::Aarch64, 65)]
        Readv,
        #[nr(Arch::X86, 88)]
        #[nr(Arch::X86_64, 169)]
        #[nr(Arch::Arm, 88)]
        #[nr(Arch::Aarch64, 142)]
        Reboot,
        #[nr(Arch::Arm, 291)]
        Recv,
        #[nr(Arch::X86, 371)]
        #[nr(Arch::X86_64, 45)]
        #[nr(Arch::Arm, 292)]
        #[nr(Arch::Aarch64, 207)]
        Recvfrom,
        #[nr(Arch::X86, 337)]
        #[nr(Arch::X86_64, 299)]
        #[nr(Arch::Arm, 365)]
        #[nr(Arch::Aarch64, 243)]
        Recvmmsg,
        #[nr(Arch::X86, 417)]
        #[nr(Arch::Arm, 417)]
        RecvmmsgTime64,
        #[nr(Arch::X86, 372)]
        #[nr(Arch::X86_64, 47)]
        #[nr(Arch::Arm, 297)]
        #[nr(Arch::Aarch64, 212)]
        Recvmsg,
        #[nr(Arch::X86, 257)]
        #[nr(Arch::X86_64, 216)]
        #[nr(Arch::Arm, 253)]
        #[nr(Arch::Aarch64, 234)]
        RemapFilePages,
        #[nr(Arch::X86, 235)]
        #[nr(Arch::X86_64, 197)]
        #[nr(Arch::Arm, 235)]
        #[nr(Arch::Aarch64, 14)]
        Removexattr,
        #[nr(Arch::X86, 466)]
        #[nr(Arch::X86_64, 466)]
        #[nr(Arch::Arm, 466)]
        #[nr(Arch::Aarch64, 466)]
        Removexattrat,
        #[nr(Arch::X86, 38)]
        #[nr(Arch::X86_64, 82)]
        #[nr(Arch::Arm, 38)]
        Rename,
        #[nr(Arch::X86, 302)]
        #[nr(Arch::X86_64, 264)]
        #[nr(Arch::Arm, 329)]
        #[nr(Arch::Aarch64, 38)]
        Renameat,
        #[nr(Arch::X86, 353)]
        #[nr(Arch::X86_64, 316)]
        #[nr(Arch::Arm, 382)]
        #[nr(Arch::Aarch64, 276)]
        Renameat2,
        #[nr(Arch::X86, 287)]
        #[nr(Arch::X86_64, 249)]
        #[nr(Arch::Arm, 310)]
        #[nr(Arch::Aarch64, 218)]
        RequestKey,
        #[nr(Arch::X86, 0)]
        #[nr(Arch::X86_64, 219)]
        #[nr(Arch::Arm, 0)]
        #[nr(Arch::Aarch64, 128)]
        RestartSyscall,
        #[nr(Arch::X86, 40)]
        #[nr(Arch::X86_64, 84)]
        #[nr(Arch::Arm, 40)]
        Rmdir,
        #[nr(Arch::X86, 386)]
        #[nr(Arch::X86_64, 334)]
        #[nr(Arch::Arm, 398)]
        #[nr(Arch::Aarch64, 293)]
        Rseq,
        #[nr(Arch::X86, 471)]
        #[nr(Arch::X86_64, 471)]
        #[nr(Arch::Arm, 471)]
        #[nr(Arch::Aarch64, 471)]
        RseqSliceYield,
        #[nr(Arch::X86, 174)]
        #[nr(Arch::X86_64, 13)]
        #[nr(Arch::Arm, 174)]
        #[nr(Arch::Aarch64, 134)]
        RtSigaction,
        #[nr(Arch::X86, 176)]
        #[nr(Arch::X86_64, 127)]
        #[nr(Arch::Arm, 176)]
        #[nr(Arch::Aarch64, 136)]
        RtSigpending,
        #[nr(Arch::X86, 175)]
        #[nr(Arch::X86_64, 14)]
        #[nr(Arch::Arm, 175)]
        #[nr(Arch::Aarch64, 135)]
        RtSigprocmask,
        #[nr(Arch::X86, 178)]
        #[nr(Arch::X86_64, 129)]
        #[nr(Arch::Arm, 178)]
        #[nr(Arch::Aarch64, 138)]
        RtSigqueueinfo,
        #[nr(Arch::X86, 173)]
        #[nr(Arch::X86_64, 15)]
        #[nr(Arch::Arm, 173)]
        #[nr(Arch::Aarch64, 139)]
        RtSigreturn,
        #[nr(Arch::X86, 179)]
        #[nr(Arch::X86_64, 130)]
        #[nr(Arch::Arm, 179)]
        #[nr(Arch::Aarch64, 133)]
        RtSigsuspend,
        #[nr(Arch::X86, 177)]
        #[nr(Arch::X86_64, 128)]
        #[nr(Arch::Arm, 177)]
        #[nr(Arch::Aarch64, 137)]
        RtSigtimedwait,
        #[nr(Arch::X86, 421)]
        #[nr(Arch::Arm, 421)]
        RtSigtimedwaitTime64,
        #[nr(Arch::X86, 335)]
        #[nr(Arch::X86_64, 297)]
        #[nr(Arch::Arm, 363)]
        #[nr(Arch::Aarch64, 240)]
        RtTgsigqueueinfo,
        #[nr(Arch::X86, 242)]
        #[nr(Arch::X86_64, 204)]
        #[nr(Arch::Arm, 242)]
        #[nr(Arch::Aarch64, 123)]
        SchedGetaffinity,
        #[nr(Arch::X86, 352)]
        #[nr(Arch::X86_64, 315)]
        #[nr(Arch::Arm, 381)]
        #[nr(Arch::Aarch64, 275)]
        SchedGetattr,
        #[nr(Arch::X86, 155)]
        #[nr(Arch::X86_64, 143)]
        #[nr(Arch::Arm, 155)]
        #[nr(Arch::Aarch64, 121)]
        SchedGetparam,
        #[nr(Arch::X86, 159)]
        #[nr(Arch::X86_64, 146)]
        #[nr(Arch::Arm, 159)]
        #[nr(Arch::Aarch64, 125)]
        SchedGetPriorityMax,
        #[nr(Arch::X86, 160)]
        #[nr(Arch::X86_64, 147)]
        #[nr(Arch::Arm, 160)]
        #[nr(Arch::Aarch64, 126)]
        SchedGetPriorityMin,
        #[nr(Arch::X86, 157)]
        #[nr(Arch::X86_64, 145)]
        #[nr(Arch::Arm, 157)]
        #[nr(Arch::Aarch64, 120)]
        SchedGetscheduler,
        #[nr(Arch::X86, 161)]
        #[nr(Arch::X86_64, 148)]
        #[nr(Arch::Arm, 161)]
        #[nr(Arch::Aarch64, 127)]
        SchedRrGetInterval,
        #[nr(Arch::X86, 423)]
        #[nr(Arch::Arm, 423)]
        SchedRrGetIntervalTime64,
        #[nr(Arch::X86, 241)]
        #[nr(Arch::X86_64, 203)]
        #[nr(Arch::Arm, 241)]
        #[nr(Arch::Aarch64, 122)]
        SchedSetaffinity,
        #[nr(Arch::X86, 351)]
        #[nr(Arch::X86_64, 314)]
        #[nr(Arch::Arm, 380)]
        #[nr(Arch::Aarch64, 274)]
        SchedSetattr,
        #[nr(Arch::X86, 154)]
        #[nr(Arch::X86_64, 142)]
        #[nr(Arch::Arm, 154)]
        #[nr(Arch::Aarch64, 118)]
        SchedSetparam,
        #[nr(Arch::X86, 156)]
        #[nr(Arch::X86_64, 144)]
        #[nr(Arch::Arm, 156)]
        #[nr(Arch::Aarch64, 119)]
        SchedSetscheduler,
        #[nr(Arch::X86, 158)]
        #[nr(Arch::X86_64, 24)]
        #[nr(Arch::Arm, 158)]
        #[nr(Arch::Aarch64, 124)]
        SchedYield,
        #[nr(Arch::X86, 354)]
        #[nr(Arch::X86_64, 317)]
        #[nr(Arch::Arm, 383)]
        #[nr(Arch::Aarch64, 277)]
        Seccomp,
        #[nr(Arch::X86_64, 185)]
        Security,
        #[nr(Arch::X86, 82)]
        #[nr(Arch::X86_64, 23)]
        Select,
        #[nr(Arch::X86, 394)]
        #[nr(Arch::X86_64, 66)]
        #[nr(Arch::Arm, 300)]
        #[nr(Arch::Aarch64, 191)]
        Semctl,
        #[nr(Arch::X86, 393)]
        #[nr(Arch::X86_64, 64)]
        #[nr(Arch::Arm, 299)]
        #[nr(Arch::Aarch64, 190)]
        Semget,
        #[nr(Arch::X86_64, 65)]
        #[nr(Arch::Arm, 298)]
        #[nr(Arch::Aarch64, 193)]
        Semop,
        #[nr(Arch::X86_64, 220)]
        #[nr(Arch::Arm, 312)]
        #[nr(Arch::Aarch64, 192)]
        Semtimedop,
        #[nr(Arch::X86, 420)]
        #[nr(Arch::Arm, 420)]
        SemtimedopTime64,
        #[nr(Arch::Arm, 289)]
        Send,
        #[nr(Arch::X86, 187)]
        #[nr(Arch::X86_64, 40)]
        #[nr(Arch::Arm, 187)]
        #[nr(Arch::Aarch64, 71)]
        Sendfile,
        #[nr(Arch::X86, 239)]
        #[nr(Arch::Arm, 239)]
        Sendfile64,
        #[nr(Arch::X86, 345)]
        #[nr(Arch::X86_64, 307)]
        #[nr(Arch::Arm, 374)]
        #[nr(Arch::Aarch64, 269)]
        Sendmmsg,
        #[nr(Arch::X86, 370)]
        #[nr(Arch::X86_64, 46)]
        #[nr(Arch::Arm, 296)]
        #[nr(Arch::Aarch64, 211)]
        Sendmsg,
        #[nr(Arch::X86, 369)]
        #[nr(Arch::X86_64, 44)]
        #[nr(Arch::Arm, 290)]
        #[nr(Arch::Aarch64, 206)]
        Sendto,
        #[nr(Arch::X86, 121)]
        #[nr(Arch::X86_64, 171)]
        #[nr(Arch::Arm, 121)]
        #[nr(Arch::Aarch64, 162)]
        Setdomainname,
        #[nr(Arch::X86, 139)]
        #[nr(Arch::X86_64, 123)]
        #[nr(Arch::Arm, 139)]
        #[nr(Arch::Aarch64, 152)]
        Setfsgid,
        #[nr(Arch::X86, 216)]
        #[nr(Arch::Arm, 216)]
        Setfsgid32,
        #[nr(Arch::X86, 138)]
        #[nr(Arch::X86_64, 122)]
        #[nr(Arch::Arm, 138)]
        #[nr(Arch::Aarch64, 151)]
        Setfsuid,
        #[nr(Arch::X86, 215)]
        #[nr(Arch::Arm, 215)]
        Setfsuid32,
        #[nr(Arch::X86, 46)]
        #[nr(Arch::X86_64, 106)]
        #[nr(Arch::Arm, 46)]
        #[nr(Arch::Aarch64, 144)]
        Setgid,
        #[nr(Arch::X86, 214)]
        #[nr(Arch::Arm, 214)]
        Setgid32,
        #[nr(Arch::X86, 81)]
        #[nr(Arch::X86_64, 116)]
        #[nr(Arch::Arm, 81)]
        #[nr(Arch::Aarch64, 159)]
        Setgroups,
        #[nr(Arch::X86, 206)]
        #[nr(Arch::Arm, 206)]
        Setgroups32,
        #[nr(Arch::X86, 74)]
        #[nr(Arch::X86_64, 170)]
        #[nr(Arch::Arm, 74)]
        #[nr(Arch::Aarch64, 161)]
        Sethostname,
        #[nr(Arch::X86, 104)]
        #[nr(Arch::X86_64, 38)]
        #[nr(Arch::Arm, 104)]
        #[nr(Arch::Aarch64, 103)]
        Setitimer,
        #[nr(Arch::X86, 276)]
        #[nr(Arch::X86_64, 238)]
        #[nr(Arch::Arm, 321)]
        #[nr(Arch::Aarch64, 237)]
        SetMempolicy,
        #[nr(Arch::X86, 450)]
        #[nr(Arch::X86_64, 450)]
        #[nr(Arch::Arm, 450)]
        #[nr(Arch::Aarch64, 450)]
        SetMempolicyHomeNode,
        #[nr(Arch::X86, 346)]
        #[nr(Arch::X86_64, 308)]
        #[nr(Arch::Arm, 375)]
        #[nr(Arch::Aarch64, 268)]
        Setns,
        #[nr(Arch::X86, 57)]
        #[nr(Arch::X86_64, 109)]
        #[nr(Arch::Arm, 57)]
        #[nr(Arch::Aarch64, 154)]
        Setpgid,
        #[nr(Arch::X86, 97)]
        #[nr(Arch::X86_64, 141)]
        #[nr(Arch::Arm, 97)]
        #[nr(Arch::Aarch64, 140)]
        Setpriority,
        #[nr(Arch::X86, 71)]
        #[nr(Arch::X86_64, 114)]
        #[nr(Arch::Arm, 71)]
        #[nr(Arch::Aarch64, 143)]
        Setregid,
        #[nr(Arch::X86, 204)]
        #[nr(Arch::Arm, 204)]
        Setregid32,
        #[nr(Arch::X86, 170)]
        #[nr(Arch::X86_64, 119)]
        #[nr(Arch::Arm, 170)]
        #[nr(Arch::Aarch64, 149)]
        Setresgid,
        #[nr(Arch::X86, 210)]
        #[nr(Arch::Arm, 210)]
        Setresgid32,
        #[nr(Arch::X86, 164)]
        #[nr(Arch::X86_64, 117)]
        #[nr(Arch::Arm, 164)]
        #[nr(Arch::Aarch64, 147)]
        Setresuid,
        #[nr(Arch::X86, 208)]
        #[nr(Arch::Arm, 208)]
        Setresuid32,
        #[nr(Arch::X86, 70)]
        #[nr(Arch::X86_64, 113)]
        #[nr(Arch::Arm, 70)]
        #[nr(Arch::Aarch64, 145)]
        Setreuid,
        #[nr(Arch::X86, 203)]
        #[nr(Arch::Arm, 203)]
        Setreuid32,
        #[nr(Arch::X86, 75)]
        #[nr(Arch::X86_64, 160)]
        #[nr(Arch::Arm, 75)]
        #[nr(Arch::Aarch64, 164)]
        Setrlimit,
        #[nr(Arch::X86, 311)]
        #[nr(Arch::X86_64, 273)]
        #[nr(Arch::Arm, 338)]
        #[nr(Arch::Aarch64, 99)]
        SetRobustList,
        #[nr(Arch::X86, 66)]
        #[nr(Arch::X86_64, 112)]
        #[nr(Arch::Arm, 66)]
        #[nr(Arch::Aarch64, 157)]
        Setsid,
        #[nr(Arch::X86, 366)]
        #[nr(Arch::X86_64, 54)]
        #[nr(Arch::Arm, 294)]
        #[nr(Arch::Aarch64, 208)]
        Setsockopt,
        #[nr(Arch::X86, 243)]
        #[nr(Arch::X86_64, 205)]
        SetThreadArea,
        #[nr(Arch::X86, 258)]
        #[nr(Arch::X86_64, 218)]
        #[nr(Arch::Arm, 256)]
        #[nr(Arch::Aarch64, 96)]
        SetTidAddress,
        #[nr(Arch::X86, 79)]
        #[nr(Arch::X86_64, 164)]
        #[nr(Arch::Arm, 79)]
        #[nr(Arch::Aarch64, 170)]
        Settimeofday,
        #[nr(Arch::Arm, 983045)]
        SetTls,
        #[nr(Arch::X86, 23)]
        #[nr(Arch::X86_64, 105)]
        #[nr(Arch::Arm, 23)]
        #[nr(Arch::Aarch64, 146)]
        Setuid,
        #[nr(Arch::X86, 213)]
        #[nr(Arch::Arm, 213)]
        Setuid32,
        #[nr(Arch::X86, 226)]
        #[nr(Arch::X86_64, 188)]
        #[nr(Arch::Arm, 226)]
        #[nr(Arch::Aarch64, 5)]
        Setxattr,
        #[nr(Arch::X86, 463)]
        #[nr(Arch::X86_64, 463)]
        #[nr(Arch::Arm, 463)]
        #[nr(Arch::Aarch64, 463)]
        Setxattrat,
        #[nr(Arch::X86, 68)]
        Sgetmask,
        #[nr(Arch::X86, 397)]
        #[nr(Arch::X86_64, 30)]
        #[nr(Arch::Arm, 305)]
        #[nr(Arch::Aarch64, 196)]
        Shmat,
        #[nr(Arch::X86, 396)]
        #[nr(Arch::X86_64, 31)]
        #[nr(Arch::Arm, 308)]
        #[nr(Arch::Aarch64, 195)]
        Shmctl,
        #[nr(Arch::X86, 398)]
        #[nr(Arch::X86_64, 67)]
        #[nr(Arch::Arm, 306)]
        #[nr(Arch::Aarch64, 197)]
        Shmdt,
        #[nr(Arch::X86, 395)]
        #[nr(Arch::X86_64, 29)]
        #[nr(Arch::Arm, 307)]
        #[nr(Arch::Aarch64, 194)]
        Shmget,
        #[nr(Arch::X86, 373)]
        #[nr(Arch::X86_64, 48)]
        #[nr(Arch::Arm, 293)]
        #[nr(Arch::Aarch64, 210)]
        Shutdown,
        #[nr(Arch::X86, 67)]
        #[nr(Arch::Arm, 67)]
        Sigaction,
        #[nr(Arch::X86, 186)]
        #[nr(Arch::X86_64, 131)]
        #[nr(Arch::Arm, 186)]
        #[nr(Arch::Aarch64, 132)]
        Sigaltstack,
        #[nr(Arch::X86, 48)]
        Signal,
        #[nr(Arch::X86, 321)]
        #[nr(Arch::X86_64, 282)]
        #[nr(Arch::Arm, 349)]
        Signalfd,
        #[nr(Arch::X86, 327)]
        #[nr(Arch::X86_64, 289)]
        #[nr(Arch::Arm, 355)]
        #[nr(Arch::Aarch64, 74)]
        Signalfd4,
        #[nr(Arch::X86, 73)]
        #[nr(Arch::Arm, 73)]
        Sigpending,
        #[nr(Arch::X86, 126)]
        #[nr(Arch::Arm, 126)]
        Sigprocmask,
        #[nr(Arch::X86, 119)]
        #[nr(Arch::Arm, 119)]
        Sigreturn,
        #[nr(Arch::X86, 72)]
        #[nr(Arch::Arm, 72)]
        Sigsuspend,
        #[nr(Arch::X86, 359)]
        #[nr(Arch::X86_64, 41)]
        #[nr(Arch::Arm, 281)]
        #[nr(Arch::Aarch64, 198)]
        Socket,
        #[nr(Arch::X86, 102)]
        Socketcall,
        #[nr(Arch::X86, 360)]
        #[nr(Arch::X86_64, 53)]
        #[nr(Arch::Arm, 288)]
        #[nr(Arch::Aarch64, 199)]
        Socketpair,
        #[nr(Arch::X86, 313)]
        #[nr(Arch::X86_64, 275)]
        #[nr(Arch::Arm, 340)]
        #[nr(Arch::Aarch64, 76)]
        Splice,
        #[nr(Arch::X86, 69)]
        Ssetmask,
        #[nr(Arch::X86, 106)]
        #[nr(Arch::X86_64, 4)]
        #[nr(Arch::Arm, 106)]
        Stat,
        #[nr(Arch::X86, 195)]
        #[nr(Arch::Arm, 195)]
        Stat64,
        #[nr(Arch::X86, 99)]
        #[nr(Arch::X86_64, 137)]
        #[nr(Arch::Arm, 99)]
        #[nr(Arch::Aarch64, 43)]
        Statfs,
        #[nr(Arch::X86, 268)]
        #[nr(Arch::Arm, 266)]
        Statfs64,
        #[nr(Arch::X86, 457)]
        #[nr(Arch::X86_64, 457)]
        #[nr(Arch::Arm, 457)]
        #[nr(Arch::Aarch64, 457)]
        Statmount,
        #[nr(Arch::X86, 383)]
        #[nr(Arch::X86_64, 332)]
        #[nr(Arch::Arm, 397)]
        #[nr(Arch::Aarch64, 291)]
        Statx,
        #[nr(Arch::X86, 25)]
        Stime,
        #[nr(Arch::X86, 31)]
        Stty,
        #[nr(Arch::X86, 115)]
        #[nr(Arch::X86_64, 168)]
        #[nr(Arch::Arm, 115)]
        #[nr(Arch::Aarch64, 225)]
        Swapoff,
        #[nr(Arch::X86, 87)]
        #[nr(Arch::X86_64, 167)]
        #[nr(Arch::Arm, 87)]
        #[nr(Arch::Aarch64, 224)]
        Swapon,
        #[nr(Arch::X86, 83)]
        #[nr(Arch::X86_64, 88)]
        #[nr(Arch::Arm, 83)]
        Symlink,
        #[nr(Arch::X86, 304)]
        #[nr(Arch::X86_64, 266)]
        #[nr(Arch::Arm, 331)]
        #[nr(Arch::Aarch64, 36)]
        Symlinkat,
        #[nr(Arch::X86, 36)]
        #[nr(Arch::X86_64, 162)]
        #[nr(Arch::Arm, 36)]
        #[nr(Arch::Aarch64, 81)]
        Sync,
        #[nr(Arch::X86, 314)]
        #[nr(Arch::X86_64, 277)]
        #[nr(Arch::Aarch64, 84)]
        SyncFileRange,
        #[nr(Arch::X86, 344)]
        #[nr(Arch::X86_64, 306)]
        #[nr(Arch::Arm, 373)]
        #[nr(Arch::Aarch64, 267)]
        Syncfs,
        #[nr(Arch::X86, 149)]
        #[nr(Arch::X86_64, 156)]
        #[nr(Arch::Arm, 149)]
        _Sysctl,
        #[nr(Arch::X86, 135)]
        #[nr(Arch::X86_64, 139)]
        #[nr(Arch::Arm, 135)]
        Sysfs,
        #[nr(Arch::X86, 116)]
        #[nr(Arch::X86_64, 99)]
        #[nr(Arch::Arm, 116)]
        #[nr(Arch::Aarch64, 179)]
        Sysinfo,
        #[nr(Arch::X86, 103)]
        #[nr(Arch::X86_64, 103)]
        #[nr(Arch::Arm, 103)]
        #[nr(Arch::Aarch64, 116)]
        Syslog,
        #[nr(Arch::X86, 315)]
        #[nr(Arch::X86_64, 276)]
        #[nr(Arch::Arm, 342)]
        #[nr(Arch::Aarch64, 77)]
        Tee,
        #[nr(Arch::X86, 270)]
        #[nr(Arch::X86_64, 234)]
        #[nr(Arch::Arm, 268)]
        #[nr(Arch::Aarch64, 131)]
        Tgkill,
        #[nr(Arch::X86, 13)]
        #[nr(Arch::X86_64, 201)]
        Time,
        #[nr(Arch::X86, 259)]
        #[nr(Arch::X86_64, 222)]
        #[nr(Arch::Arm, 257)]
        #[nr(Arch::Aarch64, 107)]
        TimerCreate,
        #[nr(Arch::X86, 263)]
        #[nr(Arch::X86_64, 226)]
        #[nr(Arch::Arm, 261)]
        #[nr(Arch::Aarch64, 111)]
        TimerDelete,
        #[nr(Arch::X86, 322)]
        #[nr(Arch::X86_64, 283)]
        #[nr(Arch::Arm, 350)]
        #[nr(Arch::Aarch64, 85)]
        TimerfdCreate,
        #[nr(Arch::X86, 326)]
        #[nr(Arch::X86_64, 287)]
        #[nr(Arch::Arm, 354)]
        #[nr(Arch::Aarch64, 87)]
        TimerfdGettime,
        #[nr(Arch::X86, 410)]
        #[nr(Arch::Arm, 410)]
        TimerfdGettime64,
        #[nr(Arch::X86, 325)]
        #[nr(Arch::X86_64, 286)]
        #[nr(Arch::Arm, 353)]
        #[nr(Arch::Aarch64, 86)]
        TimerfdSettime,
        #[nr(Arch::X86, 411)]
        #[nr(Arch::Arm, 411)]
        TimerfdSettime64,
        #[nr(Arch::X86, 262)]
        #[nr(Arch::X86_64, 225)]
        #[nr(Arch::Arm, 260)]
        #[nr(Arch::Aarch64, 109)]
        TimerGetoverrun,
        #[nr(Arch::X86, 261)]
        #[nr(Arch::X86_64, 224)]
        #[nr(Arch::Arm, 259)]
        #[nr(Arch::Aarch64, 108)]
        TimerGettime,
        #[nr(Arch::X86, 408)]
        #[nr(Arch::Arm, 408)]
        TimerGettime64,
        #[nr(Arch::X86, 260)]
        #[nr(Arch::X86_64, 223)]
        #[nr(Arch::Arm, 258)]
        #[nr(Arch::Aarch64, 110)]
        TimerSettime,
        #[nr(Arch::X86, 409)]
        #[nr(Arch::Arm, 409)]
        TimerSettime64,
        #[nr(Arch::X86, 43)]
        #[nr(Arch::X86_64, 100)]
        #[nr(Arch::Arm, 43)]
        #[nr(Arch::Aarch64, 153)]
        Times,
        #[nr(Arch::X86, 238)]
        #[nr(Arch::X86_64, 200)]
        #[nr(Arch::Arm, 238)]
        #[nr(Arch::Aarch64, 130)]
        Tkill,
        #[nr(Arch::X86, 92)]
        #[nr(Arch::X86_64, 76)]
        #[nr(Arch::Arm, 92)]
        #[nr(Arch::Aarch64, 45)]
        Truncate,
        #[nr(Arch::X86, 193)]
        #[nr(Arch::Arm, 193)]
        Truncate64,
        #[nr(Arch::X86_64, 184)]
        Tuxcall,
        #[nr(Arch::X86, 191)]
        #[nr(Arch::Arm, 191)]
        Ugetrlimit,
        #[nr(Arch::X86, 58)]
        Ulimit,
        #[nr(Arch::X86, 60)]
        #[nr(Arch::X86_64, 95)]
        #[nr(Arch::Arm, 60)]
        #[nr(Arch::Aarch64, 166)]
        Umask,
        #[nr(Arch::X86, 22)]
        Umount,
        #[nr(Arch::X86, 52)]
        #[nr(Arch::X86_64, 166)]
        #[nr(Arch::Arm, 52)]
        #[nr(Arch::Aarch64, 39)]
        Umount2,
        #[nr(Arch::X86, 122)]
        #[nr(Arch::X86_64, 63)]
        #[nr(Arch::Arm, 122)]
        #[nr(Arch::Aarch64, 160)]
        Uname,
        #[nr(Arch::X86, 10)]
        #[nr(Arch::X86_64, 87)]
        #[nr(Arch::Arm, 10)]
        Unlink,
        #[nr(Arch::X86, 301)]
        #[nr(Arch::X86_64, 263)]
        #[nr(Arch::Arm, 328)]
        #[nr(Arch::Aarch64, 35)]
        Unlinkat,
        #[nr(Arch::X86, 310)]
        #[nr(Arch::X86_64, 272)]
        #[nr(Arch::Arm, 337)]
        #[nr(Arch::Aarch64, 97)]
        Unshare,
        #[nr(Arch::X86_64, 336)]
        Uprobe,
        #[nr(Arch::X86_64, 335)]
        Uretprobe,
        #[nr(Arch::X86, 86)]
        #[nr(Arch::X86_64, 134)]
        #[nr(Arch::Arm, 86)]
        Uselib,
        #[nr(Arch::X86, 374)]
        #[nr(Arch::X86_64, 323)]
        #[nr(Arch::Arm, 388)]
        #[nr(Arch::Aarch64, 282)]
        Userfaultfd,
        #[nr(Arch::Arm, 983043)]
        Usr26,
        #[nr(Arch::Arm, 983044)]
        Usr32,
        #[nr(Arch::X86, 62)]
        #[nr(Arch::X86_64, 136)]
        #[nr(Arch::Arm, 62)]
        Ustat,
        #[nr(Arch::X86, 30)]
        #[nr(Arch::X86_64, 132)]
        Utime,
        #[nr(Arch::X86, 320)]
        #[nr(Arch::X86_64, 280)]
        #[nr(Arch::Arm, 348)]
        #[nr(Arch::Aarch64, 88)]
        Utimensat,
        #[nr(Arch::X86, 412)]
        #[nr(Arch::Arm, 412)]
        UtimensatTime64,
        #[nr(Arch::X86, 271)]
        #[nr(Arch::X86_64, 235)]
        #[nr(Arch::Arm, 269)]
        Utimes,
        #[nr(Arch::X86, 190)]
        #[nr(Arch::X86_64, 58)]
        #[nr(Arch::Arm, 190)]
        Vfork,
        #[nr(Arch::X86, 111)]
        #[nr(Arch::X86_64, 153)]
        #[nr(Arch::Arm, 111)]
        #[nr(Arch::Aarch64, 58)]
        Vhangup,
        #[nr(Arch::X86, 166)]
        Vm86,
        #[nr(Arch::X86, 113)]
        Vm86old,
        #[nr(Arch::X86, 316)]
        #[nr(Arch::X86_64, 278)]
        #[nr(Arch::Arm, 343)]
        #[nr(Arch::Aarch64, 75)]
        Vmsplice,
        #[nr(Arch::X86, 273)]
        #[nr(Arch::X86_64, 236)]
        #[nr(Arch::Arm, 313)]
        Vserver,
        #[nr(Arch::X86, 114)]
        #[nr(Arch::X86_64, 61)]
        #[nr(Arch::Arm, 114)]
        #[nr(Arch::Aarch64, 260)]
        Wait4,
        #[nr(Arch::X86, 284)]
        #[nr(Arch::X86_64, 247)]
        #[nr(Arch::Arm, 280)]
        #[nr(Arch::Aarch64, 95)]
        Waitid,
        #[nr(Arch::X86, 7)]
        Waitpid,
        #[nr(Arch::X86, 4)]
        #[nr(Arch::X86_64, 1)]
        #[nr(Arch::Arm, 4)]
        #[nr(Arch::Aarch64, 64)]
        Write,
        #[nr(Arch::X86, 146)]
        #[nr(Arch::X86_64, 20)]
        #[nr(Arch::Arm, 146)]
        #[nr(Arch::Aarch64, 66)]
        Writev,
        // A special syscall to indicate it has been skipped.
        #[nr(Arch::X86, -1)]
        #[nr(Arch::X86_64, -1)]
        #[nr(Arch::Arm, -1)]
        #[nr(Arch::Aarch64, -1)]
        Skip,
    }
}

impl Syscall {
    /// `SYS_*` from `linux/net.h`: the call number under which x86 reaches this syscall through `socketcall`.
    pub open spec fn to_socketcall_arg(self) -> Option<u64> {
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
 
    /// `linux/ipc.h`: the call number under which x86 reaches this syscall through `ipc`.
    pub open spec fn to_ipc_arg(self) -> Option<u64> {
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

} // verus!
