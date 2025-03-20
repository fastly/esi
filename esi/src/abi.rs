use crate::vm_types::*;
use compiler_macros::abi_fn;
use std::ops::Range;

#[derive(Debug, Clone, PartialEq)]
pub enum Args {
    Constant(usize),
    Variadic,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnSignature {
    pub args: Args,
    pub has_return: bool,
}

pub type AbiFn = fn(usize, &mut ExecutionState);

#[derive(Debug, Clone, PartialEq)]
pub struct BuiltinFn {
    func: AbiFn,
    sig: FnSignature,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MetaVar {/* fieldless metavar names go here */}

#[derive(Debug, Clone, PartialEq)]
pub struct Abi<'a> {
    pub version: u32,
    functions: &'a [(&'a str, BuiltinFn)],
    meta_vars: &'a [MetaVar],
}

pub const ABI_TEST: Abi<'static> = Abi {
    version: 0,
    functions: &[
        ("ping", ping_builtin),
        ("identity", identity_builtin),
        ("make_list", make_list_builtin),
    ],
    meta_vars: &[],
};

pub const ABI_V1: Abi<'static> = Abi {
    version: 1,
    functions: &[],
    meta_vars: &[],
};

impl Abi<'static> {
    pub fn for_version(version: u32) -> Result<&'static Abi<'static>> {
        match version {
            0 => Ok(&ABI_TEST),
            1 => Ok(&ABI_V1),
            _ => Err(VMError(format!("unknown version: {}", version))),
        }
    }

    pub fn function_by_name(&self, fn_name: &'_ str) -> Option<(u32, &'static FnSignature)> {
        // TODO: fix types here, should be FunctionId
        match self.functions.iter().position(|(name, _)| fn_name == *name) {
            None => None,
            Some(idx) => Some((idx as u32, &self.functions[idx].1.sig)),
        }
    }

    pub fn call_function(&self, func_id: usize, args_len: usize, state: &mut ExecutionState) {
        let (_, builtin) = &self.functions[func_id];
        (builtin.func)(args_len, state);
    }
}

// ABI Functions

#[abi_fn(args = 0, has_return = true)]
fn ping(args: usize, state: &mut ExecutionState) {
    if args > 0 {
        //state.die();
    }

    state.push(Value::String("pong".as_bytes().to_vec()));
}

#[abi_fn(args = 1, has_return = true)]
fn identity(args: usize, state: &mut ExecutionState) {
    if args != 1 {
        //state.die();
    }

    let value = state.pop_value().clone();
    state.push(value);
}

#[abi_fn(args = N, has_return = true)]
fn make_list(args: usize, state: &mut ExecutionState) {
    let values: Vec<Value> = (0..args).map(|_| state.pop_value().clone()).collect();
    state.push(Value::List(values));
}
