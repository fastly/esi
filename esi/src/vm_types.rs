pub unsafe fn read_u64(ptr: *const u8) -> u64 {
    ptr.cast::<u64>().read_unaligned()
}
pub unsafe fn read_u32(ptr: *const u8) -> u32 {
    ptr.cast::<u32>().read_unaligned()
}

pub const MAGIC: u32 = 0xABADBABA;

#[derive(Debug, Clone)]
pub struct VMError(pub String);
pub type Result<T> = std::result::Result<T, VMError>;

#[derive(Debug, Clone)]
pub enum Value {
    Null,
    LiteralString(*const u8), // Pointer to length-prepended string in code segment
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
        }
    }

    pub fn to_bool(&self) -> bool {
        match self {
            Value::Null => false,
            lit_str @ Value::LiteralString(_) => lit_str.to_bytes().len() == 0,
            Value::Bool(b) => *b,
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        match self {
            Value::Null => match other {
                Value::Null => true,
                Value::LiteralString(_) => false,
                Value::Bool(_) => false, // TODO: not sure if null == false
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
                Value::Null => false,
                Value::Bool(_) => false, // TODO: might need to coerce the bool to a string here
            },
            Value::Bool(self_b) => match other {
                Value::Bool(other_b) => self_b == other_b,
                Value::Null => false,
                Value::LiteralString(_) => false, // TODO: ditto above re: coercion
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
    // requests
}
