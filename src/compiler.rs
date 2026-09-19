//! A simple compiler from policies to cBPF programs.

use vstd::prelude::*;
use crate::spec::{policy::*, cbpf::*};

verus! {

pub enum CompileError {
    PolicyTooLarge,
}

impl Policy {
    pub fn lower(&self) -> (res: Result<Program, CompileError>)
        requires self.wf()
        ensures res matches Ok(prog) ==>
            // Compiled program is well-formed.
            prog.wf() &&
            // Compiled program runs error-free and produces an action accepted by the policy.
            forall |data: &[u8]| #[trigger] Event::parse(data) matches Some(ev) ==> {
                &&& prog.eval(data) matches Outcome::Return(ret)
                &&& self.eval(ev, Action::from_ret(ret))
            }
    {
        assume(false);
        todo!()
    }
}

}
