//! Some glue code to compile/install a policy with `seccomp(2)`.

use vstd::prelude::*;
use crate::spec::{policy::*, cbpf::*};
use crate::compiler::CompileError;

verus! {

#[verifier::external_type_specification]
#[allow(dead_code)]
struct ExSockFilter(libc::sock_filter);

pub enum InstallError {
    Compile(CompileError),
    NoNewPrivs(i32),
    SetModeFilter(i32),
}

impl InstallError {
    /// The errno the last failing libc call left behind.
    #[verifier::external_body]
    fn errno() -> i32 {
        std::io::Error::last_os_error().raw_os_error().unwrap_or(0)
    }
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

    pub fn assemble(&self) -> libc::sock_filter {
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
        libc::sock_filter { code, jt, jf, k }
    }
}

impl Attrs {
    /// The `SECCOMP_FILTER_FLAG_*` bits in `linux/seccomp.h`.
    const FLAG_TSYNC: u64 = 1 << 0;
    const FLAG_LOG: u64 = 1 << 1;
    const FLAG_SPEC_ALLOW: u64 = 1 << 2;

    /// The flag word these attributes ask `seccomp(2)` for.
    fn filter_flags(&self) -> u64 {
        let mut flags: u64 = 0;
        if self.ctl_tsync {
            flags = flags | Self::FLAG_TSYNC;
        }
        if self.ctl_log {
            flags = flags | Self::FLAG_LOG;
        }
        if self.ctl_ssb {
            flags = flags | Self::FLAG_SPEC_ALLOW;
        }
        // `ctl_waitkill` has nothing to wait on without `SECCOMP_FILTER_FLAG_NEW_LISTENER`,
        // and this module opens no notification listener.
        flags
    }
}

impl Program {
    /// Loads this program into the calling thread as its seccomp filter.
    #[verifier::external_body]
    pub fn install(&self, attrs: &Attrs) -> Result<(), InstallError> {
        // `seccomp()` answers EACCES to a thread that holds neither CAP_SYS_ADMIN nor
        // `no_new_privs`, so `ctl_nnp` goes in first.
        if attrs.ctl_nnp {
            let rc = unsafe { libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) };
            if rc != 0 {
                return Err(InstallError::NoNewPrivs(InstallError::errno()));
            }
        }

        let mut filter: Vec<libc::sock_filter> = Vec::with_capacity(self.instrs.len());
        for instr in self.instrs.iter() {
            filter.push(instr.assemble());
        }

        // The kernel copies the program out of `sock_fprog` before it returns, so the
        // buffer only has to outlive the call.
        let fprog = libc::sock_fprog {
            len: filter.len() as u16,
            filter: filter.as_mut_ptr(),
        };
        let rc = unsafe {
            libc::syscall(
                libc::SYS_seccomp,
                libc::SECCOMP_SET_MODE_FILTER as libc::c_ulong,
                attrs.filter_flags() as libc::c_ulong,
                &fprog as *const libc::sock_fprog,
            )
        };
        if rc != 0 {
            // A thread that refuses TSYNC comes back as its own id rather than as -1,
            // unless `SECCOMP_FILTER_FLAG_TSYNC_ESRCH` is set, which this module leaves off.
            let errno = if rc < 0 { InstallError::errno() } else { libc::ESRCH };
            return Err(InstallError::SetModeFilter(errno));
        }
        Ok(())
    }
}

impl Policy {
    /// Compiles this policy and loads it into the calling thread as its seccomp filter.
    pub fn install(&self) -> Result<(), InstallError>
        requires self.wf()
    {
        match self.lower() {
            Ok(prog) => prog.install(&self.attrs),
            Err(err) => Err(InstallError::Compile(err)),
        }
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    /// How a child process that ran under a policy ended.
    #[derive(Debug, PartialEq, Eq)]
    enum Child {
        /// Left through `_exit` with this status.
        Exited(i32),
        /// Killed by this signal.
        Killed(i32),
    }

    impl Child {
        /// The status the child leaves with when the policy never reaches the kernel.
        const INSTALL_FAILED: i32 = 70;

        /// Runs `body` in a child process that has `policy` installed.
        fn run(policy: &Policy, body: impl FnOnce() -> i32) -> Child {
            unsafe {
                let pid = libc::fork();
                assert!(pid >= 0, "fork failed");
                if pid == 0 {
                    // A denied exit would leave the child spinning, so cap how long it lives.
                    libc::alarm(10);
                    let status = match policy.install() {
                        Ok(()) => body(),
                        Err(_) => Self::INSTALL_FAILED,
                    };
                    libc::_exit(status);
                }
                let mut status: libc::c_int = 0;
                assert_eq!(libc::waitpid(pid, &mut status, 0), pid, "waitpid failed");
                if libc::WIFSIGNALED(status) {
                    Child::Killed(libc::WTERMSIG(status))
                } else {
                    Child::Exited(libc::WEXITSTATUS(status))
                }
            }
        }
    }

    impl Arch {
        /// The architecture this test binary runs on.
        fn native() -> Arch {
            if cfg!(target_arch = "x86_64") {
                Arch::X86_64
            } else if cfg!(target_arch = "aarch64") {
                Arch::Aarch64
            } else if cfg!(target_arch = "x86") {
                Arch::X86
            } else if cfg!(target_arch = "arm") {
                Arch::Arm
            } else {
                panic!("no Arch for this target")
            }
        }
    }

    impl Policy {
        /// A policy over the running architecture that lets through whatever `rules` leave alone.
        fn allow_except(rules: Vec<Rule>) -> Policy {
            Policy {
                attrs: Attrs { act_default: Action::Allow, ..Attrs::default() },
                archs: vec![Arch::native()],
                priorities: vec![],
                rules,
            }
        }
    }

    impl Rule {
        /// A rule that answers `action` to `name` under `conds`.
        fn new(action: Action, name: SyscallName, conds: Vec<ArgCmp>) -> Rule {
            Rule { action, syscall: Syscall::Name(name), conds, exact: false }
        }
    }

    /// A policy with no rules and an `SCMP_ACT_ALLOW` default lets the child run on.
    #[test]
    fn allow_all() {
        let policy = Policy::allow_except(vec![]);
        let child = Child::run(&policy, || unsafe {
            if libc::syscall(libc::SYS_getpid) > 0 { 0 } else { 1 }
        });
        assert_eq!(child, Child::Exited(0));
    }

    /// An `SCMP_ACT_ERRNO` rule fails its own syscall and no other.
    #[test]
    fn errno_on_getpid() {
        let policy = Policy::allow_except(vec![
            Rule::new(Action::Errno(libc::EPERM as u16), SyscallName::Getpid, vec![]),
        ]);
        let child = Child::run(&policy, || unsafe {
            if libc::syscall(libc::SYS_getpid) != -1 { return 1; }
            if InstallError::errno() != libc::EPERM { return 2; }
            if libc::syscall(libc::SYS_getppid) <= 0 { return 3; }
            0
        });
        assert_eq!(child, Child::Exited(0));
    }

    /// An `SCMP_ACT_KILL_PROCESS` rule takes the child down with SIGSYS.
    #[test]
    fn kill_process_on_getppid() {
        let policy = Policy::allow_except(vec![
            Rule::new(Action::KillProcess, SyscallName::Getppid, vec![]),
        ]);
        let child = Child::run(&policy, || unsafe {
            libc::syscall(libc::SYS_getppid);
            0
        });
        assert_eq!(child, Child::Killed(libc::SIGSYS));
    }

    /// An argument test narrows a rule to the calls that pass it.
    #[test]
    fn errno_on_first_argument() {
        let policy = Policy::allow_except(vec![
            Rule::new(Action::Errno(libc::EPERM as u16), SyscallName::Lseek, vec![
                ArgCmp { arg: 0, op: Compare::Eq, datum_a: 42, datum_b: 0 },
            ]),
        ]);
        let child = Child::run(&policy, || {
            // `lseek` on a descriptor nothing opened, which the kernel refuses with EBADF.
            let lseek = |fd: libc::c_long, offset: libc::c_long| unsafe {
                libc::syscall(libc::SYS_lseek, fd, offset, libc::SEEK_SET as libc::c_long)
            };
            if lseek(42, 0) != -1 { return 1; }
            if InstallError::errno() != libc::EPERM { return 2; }
            if lseek(43, 0) != -1 { return 3; }
            if InstallError::errno() != libc::EBADF { return 4; }
            0
        });
        assert_eq!(child, Child::Exited(0));
    }

    /// An argument test on a 64-bit architecture looks at both words of the argument.
    #[test]
    fn errno_on_high_word_of_argument() {
        let policy = Policy::allow_except(vec![
            Rule::new(Action::Errno(libc::EPERM as u16), SyscallName::Lseek, vec![
                ArgCmp { arg: 1, op: Compare::Eq, datum_a: 0x1_0000_0000, datum_b: 0 },
            ]),
        ]);
        let child = Child::run(&policy, || {
            // `lseek` on a descriptor nothing opened, which the kernel refuses with EBADF.
            let lseek = |fd: libc::c_long, offset: libc::c_long| unsafe {
                libc::syscall(libc::SYS_lseek, fd, offset, libc::SEEK_SET as libc::c_long)
            };
            if lseek(43, 0x1_0000_0000) != -1 { return 1; }
            if InstallError::errno() != libc::EPERM { return 2; }
            if lseek(43, 1) != -1 { return 3; }
            if InstallError::errno() != libc::EBADF { return 4; }
            0
        });
        assert_eq!(child, Child::Exited(0));
    }

    /// An event from an architecture the policy leaves out takes `act_badarch`.
    #[test]
    fn badarch_kills() {
        let absent = if Arch::native() == Arch::X86 { Arch::Aarch64 } else { Arch::X86 };
        let policy = Policy {
            attrs: Attrs {
                act_default: Action::Allow,
                act_badarch: Action::KillProcess,
                ..Attrs::default()
            },
            archs: vec![absent],
            priorities: vec![],
            rules: vec![],
        };
        let child = Child::run(&policy, || unsafe {
            libc::syscall(libc::SYS_getpid);
            0
        });
        assert_eq!(child, Child::Killed(libc::SIGSYS));
    }
}
