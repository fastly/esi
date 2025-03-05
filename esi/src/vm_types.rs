pub unsafe fn read_u64(ptr: *const u8) -> u64 {
    ptr.cast::<u64>().read_unaligned()
}
pub unsafe fn read_u32(ptr: *const u8) -> u32 {
    ptr.cast::<u32>().read_unaligned()
}
pub unsafe fn read_u16(ptr: *const u8) -> u16 {
    ptr.cast::<u16>().read_unaligned()
}

pub const MAGIC: u32 = 0xABADBABA;

#[derive(Debug, Clone)]
pub struct VMError(pub String);
pub type Result<T> = std::result::Result<T, VMError>;

#[derive(Debug, Clone)]
pub enum Value {
    Null,
    LiteralString(*const u8), // Pointer to length-prepended string in code segment
    String(Vec<u8>),
    Bool(bool),
}

impl Value {
    pub fn to_bytes(&self) -> &[u8] {
        match self {
            Value::Null => b"(null)",
            Value::LiteralString(ptr) => unsafe {
                let len = read_u32(*ptr);
                std::slice::from_raw_parts(ptr.add(4), len as usize)
            },
            Value::Bool(b) => {
                if *b {
                    b"true"
                } else {
                    b"false"
                }
            }
            Value::String(s) => &s,
        }
    }

    pub fn to_bool(&self) -> bool {
        match self {
            Value::Null => false,
            lit_str @ Value::LiteralString(_) => lit_str.to_bytes().len() == 0,
            Value::String(s) => s.len() == 0,
            Value::Bool(b) => *b,
        }
    }

    pub fn add(self, other: Value) -> Value {
        match self {
            Value::Null => match other {
                Value::Null => Value::Null,
                v @ Value::LiteralString(_) => v.clone(),
                Value::Bool(_) => todo!(),
                Value::String(_) => todo!(),
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
                    out.extend_from_slice(self_lit_str.to_bytes());
                    out.extend_from_slice(&other_str);
                    Value::String(out)
                }
            },
            Value::Bool(self_b) => match other {
                Value::Bool(other_b) => todo!(),
                Value::Null => todo!(),
                Value::LiteralString(_) => todo!(),
                Value::String(_) => todo!(),
            },
            Value::String(self_str) => match other {
                Value::Bool(other_b) => todo!(),
                Value::Null => todo!(),
                other_lit_str @ Value::LiteralString(_) => {
                    let mut out = Vec::new();
                    out.extend_from_slice(&self_str);
                    out.extend_from_slice(other_lit_str.to_bytes());
                    Value::String(out)
                }
                Value::String(_) => todo!(),
            },
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
            },
            Value::Bool(self_b) => match other {
                Value::Bool(other_b) => self_b == other_b,
                Value::Null => false,
                Value::LiteralString(_) => false, // TODO: ditto above re: coercion
                Value::String(_) => false,        // TODO: ditto above re: coercion
            },
            Value::String(self_str) => match other {
                Value::Bool(other_b) => todo!(),
                Value::Null => false,
                Value::LiteralString(_) => todo!(),
                Value::String(other_str) => self_str == other_str,
            },
        }
    }
}

#[derive(Debug, Clone)]
pub enum BuiltinFn {/* fieldless builtins go here */}

#[derive(Debug, Clone)]
pub enum MetaVar {/* fieldless metavar names go here */}

#[derive(Debug, Clone)]
pub struct Environment<'a> {
    /* request: Request, */
    functions: &'a [BuiltinFn],
    meta_vars: &'a [MetaVar],
}

const ENVIRONMENT_V1: Environment<'static> = Environment {
    functions: &[],
    meta_vars: &[],
};

impl Environment<'_> {
    pub fn for_version(version: u32) -> Result<Self> {
        match version {
            1 => Ok(ENVIRONMENT_V1),
            _ => Err(VMError(format!("unknown version: {}", version))),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ProgramContext<'a> {
    pub program_data: &'a [u8],
    pub variable_count: usize,
    pub request_count: usize,
    pub code_length: usize,
    pub code_ptr: *const u8,
    pub data: &'a [u8],
}

#[derive(Debug, Clone)]
pub struct ExecutionState {
    pub ip: usize,
    pub stack: Vec<Value>,
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

    fn write_bytes(&self, data: &[u8]);

    fn write_response(&self, response: &Response);
}
