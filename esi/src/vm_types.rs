pub unsafe fn read_u64(ptr: *const u8) -> u64 {
    ptr.cast::<u64>().read_unaligned()
}
pub unsafe fn read_u32(ptr: *const u8) -> u32 {
    ptr.cast::<u32>().read_unaligned()
}
pub unsafe fn read_i32(ptr: *const u8) -> i32 {
    ptr.cast::<i32>().read_unaligned()
}
pub unsafe fn read_u16(ptr: *const u8) -> u16 {
    ptr.cast::<u16>().read_unaligned()
}

use crate::abi::*;

pub const MAGIC: u32 = 0xABADBABA;

#[derive(Debug, Clone)]
pub struct VMError(pub String);
pub type Result<T> = std::result::Result<T, VMError>;

#[derive(Debug, Clone)]
pub enum StackEntry {
    Value(Value),
    Ref(usize),
}

impl StackEntry {
    pub fn to_value(self, state: &ExecutionState) -> Value {
        match self {
            StackEntry::Value(v) => v,
            StackEntry::Ref(varid) => state.variables[varid].clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Null,
    LiteralString(*const u8), // Pointer to length-prepended string in code segment
    String(Vec<u8>),
    Bool(bool),
    Integer(i32),
    List(Vec<Value>),
}

impl Value {
    pub fn to_bytes(&self) -> Vec<u8> {
        match self {
            Value::Null => b"".to_vec(),
            Value::LiteralString(ptr) => unsafe {
                let len = read_u32(*ptr);
                std::slice::from_raw_parts(ptr.add(4), len as usize).to_owned()
            },
            Value::Bool(b) => {
                if *b {
                    b"true".to_vec()
                } else {
                    b"false".to_vec()
                }
            }
            Value::String(s) => s.clone(),
            Value::Integer(i) => i.to_string().into_bytes(),
            Value::List(_) => todo!(),
        }
    }

    pub fn to_bool(&self) -> bool {
        match self {
            Value::Null => false,
            lit_str @ Value::LiteralString(_) => lit_str.to_bytes().len() == 0,
            Value::String(s) => s.len() == 0,
            Value::Bool(b) => *b,
            Value::Integer(i) => *i != 0,
            Value::List(_) => todo!(),
        }
    }

    pub fn add(self, other: Value) -> Value {
        match self {
            Value::Null => match other {
                Value::Null => Value::Null,
                v @ Value::LiteralString(_) => v.clone(),
                Value::Bool(_) => todo!(),
                Value::String(_) => todo!(),
                Value::Integer(_) => todo!(),
                Value::List(_) => todo!(),
            },
            self_lit_str @ Value::LiteralString(self_ptr) => match other {
                Value::LiteralString(other_ptr) => unsafe {
                    let self_len = read_u32(self_ptr) as usize;
                    let other_len = read_u32(other_ptr) as usize;
                    let mut out = Vec::with_capacity(self_len + other_len);
                    let dst = out.as_mut_ptr();

                    std::ptr::copy_nonoverlapping(self_ptr.add(4), dst, self_len);
                    std::ptr::copy_nonoverlapping(other_ptr.add(4), dst.add(self_len), other_len);

                    out.set_len(self_len + other_len);

                    Value::String(out)
                },
                Value::Null => self_lit_str.clone(),
                Value::Bool(_) => todo!(), // TODO: might need to coerce the bool to a string here
                Value::String(other_str) => {
                    let mut out = Vec::new();
                    out.extend_from_slice(&self_lit_str.to_bytes());
                    out.extend_from_slice(&other_str);
                    Value::String(out)
                }
                Value::Integer(_) => todo!(),
                Value::List(_) => todo!(),
            },
            Value::Bool(self_b) => match other {
                Value::Bool(other_b) => todo!(),
                Value::Null => todo!(),
                Value::LiteralString(_) => todo!(),
                Value::String(_) => todo!(),
                Value::Integer(_) => todo!(),
                Value::List(_) => todo!(),
            },
            Value::String(self_str) => match other {
                Value::Bool(other_b) => todo!(),
                Value::Null => todo!(),
                other_lit_str @ Value::LiteralString(_) => {
                    let mut out = Vec::new();
                    out.extend_from_slice(&self_str);
                    out.extend_from_slice(&other_lit_str.to_bytes());
                    Value::String(out)
                }
                Value::String(_) => todo!(),
                Value::Integer(_) => todo!(),
                Value::List(_) => todo!(),
            },
            Value::Integer(self_i) => match other {
                Value::Bool(other_b) => todo!(),
                Value::Null => todo!(),
                Value::LiteralString(_) => todo!(),
                Value::String(_) => todo!(),
                Value::Integer(other_i) => Value::Integer(self_i + other_i),
                Value::List(_) => todo!(),
            },
            Value::List(_) => todo!(),
        }
    }

    pub fn subtract(self, other: Value) -> Value {
        match self {
            Value::Integer(self_i) => match other {
                Value::Integer(other_i) => Value::Integer(self_i - other_i),
                _ => Value::Null,
            },
            _ => Value::Null,
        }
    }
    pub fn divide(self, other: Value) -> Value {
        match self {
            Value::Integer(self_i) => match other {
                Value::Integer(other_i) => Value::Integer(self_i / other_i),
                _ => Value::Null,
            },
            _ => Value::Null,
        }
    }
    pub fn multiply(self, other: Value) -> Value {
        match self {
            Value::Integer(self_i) => match other {
                Value::Integer(other_i) => Value::Integer(self_i * other_i),
                _ => Value::Null,
            },
            _ => Value::Null,
        }
    }
    pub fn modulo(self, other: Value) -> Value {
        match self {
            Value::Integer(self_i) => match other {
                Value::Integer(other_i) => Value::Integer(self_i % other_i),
                _ => Value::Null,
            },
            _ => Value::Null,
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        match self {
            Value::Null => match other {
                Value::Null => true,
                Value::LiteralString(_) => false, // TODO: empty string might equal null?
                Value::String(_) => false,        // TODO: empty string might equal null?
                Value::Bool(_) => false,          // TODO: not sure if null == false
                Value::Integer(_) => todo!(),
                Value::List(_) => todo!(),
            },
            Value::LiteralString(self_ptr) => match other {
                Value::LiteralString(other_ptr) => {
                    if *self_ptr == *other_ptr {
                        // Same pointer, same string
                        true
                    } else {
                        // Otherwise, bytewise comparison
                        self.to_bytes() == other.to_bytes()
                    }
                }
                Value::String(other_str) => self.to_bytes() == *other_str,
                Value::Null => false,
                Value::Bool(_) => false, // TODO: might need to coerce the bool to a string here
                Value::Integer(_) => self.to_bytes() == other.to_bytes(),
                Value::List(_) => todo!(),
            },
            Value::Bool(self_b) => match other {
                Value::Bool(other_b) => self_b == other_b,
                Value::Null => false,
                Value::LiteralString(_) => false, // TODO: ditto above re: coercion
                Value::String(_) => false,        // TODO: ditto above re: coercion
                Value::Integer(_) => false,
                Value::List(_) => todo!(),
            },
            Value::String(self_str) => match other {
                Value::Bool(other_b) => todo!(),
                Value::Null => false,
                Value::LiteralString(_) => todo!(),
                Value::String(other_str) => self_str == other_str,
                Value::Integer(_) => self.to_bytes() == other.to_bytes(),
                Value::List(_) => todo!(),
            },
            Value::Integer(self_i) => match other {
                Value::Bool(other_b) => todo!(),
                Value::Null => todo!(),
                Value::LiteralString(_) => todo!(),
                Value::String(other_str) => self_i.to_string().into_bytes() == *other_str,
                Value::Integer(other_i) => self_i == other_i,
                Value::List(_) => todo!(),
            },
            Value::List(_) => todo!(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ProgramContext<'a> {
    pub program_data: &'a [u8],
    pub abi_version: u32,
    pub variable_count: usize,
    pub request_count: usize,
    pub code_length: usize,
    pub code_ptr: *const u8,
    pub data: &'a [u8],
}

#[derive(Debug, Clone)]
pub struct ExecutionState {
    pub ip: usize,
    stack: Vec<StackEntry>,
    pub variables: Vec<Value>,
    pub requests: Vec<RequestHandle>,
}
impl ExecutionState {
    pub fn new(ctx: &ProgramContext) -> Self {
        Self {
            ip: 0,
            stack: Vec::new(), // TODO: bleh
            variables: vec![Value::Null; ctx.variable_count],
            requests: vec![NO_REQUEST_HANDLE; ctx.request_count],
        }
    }
    pub fn push(&mut self, v: Value) {
        self.stack.push(StackEntry::Value(v));
    }

    pub fn push_ref(&mut self, varid: usize) {
        self.stack.push(StackEntry::Ref(varid));
    }

    pub fn pop(&mut self) -> StackEntry {
        self.stack.pop().unwrap()
    }

    pub fn pop_value(&mut self) -> Value {
        let entry = self.stack.pop().unwrap();
        entry.to_value(self)
    }
}

pub type RequestHandle = u64;
const NO_REQUEST_HANDLE: RequestHandle = u64::MAX;

#[derive(Debug, Clone, PartialEq)]
pub enum Response {
    Success,
    Failure,
}

pub trait EnvironmentApi {
    fn request(&self, url: &[u8]) -> RequestHandle;

    fn get_response(&self, handle: RequestHandle) -> Response;

    fn write_bytes(&mut self, data: &[u8]);

    fn write_response(&mut self, response: &Response);
}
