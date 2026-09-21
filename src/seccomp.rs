//! Some glue code to compile/install a policy with `seccomp(2)`.

use vstd::prelude::*;
use crate::spec::{policy::*, cbpf::*};
use crate::asm::SockFilter;
use crate::compiler::CompileError;

verus! {

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

        let mut filter: Vec<SockFilter> = self.assemble();

        // The kernel copies the program out of `sock_fprog` before it returns, so the
        // buffer only has to outlive the call.
        let fprog = libc::sock_fprog {
            len: filter.len() as u16,
            filter: filter.as_mut_ptr() as *mut libc::sock_filter,
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
        match self.to_cbpf() {
            Ok(prog) => prog.install(&self.attrs),
            Err(err) => Err(InstallError::Compile(err)),
        }
    }
}

} // verus!
