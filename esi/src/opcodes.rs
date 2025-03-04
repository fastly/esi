use compiler_macros::Constraints;

#[repr(u8)]
#[derive(Debug, Clone, PartialEq, Constraints)]
pub enum Opcode {
    #[meta(name = "write_bytes", stack_args = 0, immediates = 1, returns = 0)]
    WriteBytes = 1,

    #[meta(name = "write_response", stack_args = 0, immediates = 1, returns = 0)]
    WriteResponse = 2,

    #[meta(name = "write_value", stack_args = 1, immediates = 0, returns = 0)]
    WriteValue = 3,

    #[meta(name = "request", stack_args = 1, immediates = 1, returns = 0)]
    Request = 4,

    #[meta(name = "success", stack_args = 0, immediates = 1, returns = 1)]
    Success = 5,

    #[meta(name = "jump", stack_args = 0, immediates = 1, returns = 0)]
    Jump = 6,

    #[meta(name = "jump_if", stack_args = 1, immediates = 1, returns = 0)]
    JumpIf = 7,

    #[meta(name = "set", stack_args = 1, immediates = 1, returns = 0)]
    Set = 8,

    #[meta(name = "get", stack_args = 0, immediates = 1, returns = 1)]
    Get = 9,

    #[meta(name = "get_meta", stack_args = 0, immediates = 0, returns = 1)]
    GetMeta = 10, // TODO

    #[meta(name = "set_key", stack_args = 3, immediates = 0, returns = 0)]
    SetKey = 11,

    #[meta(name = "get_key", stack_args = 2, immediates = 0, returns = 1)]
    GetKey = 12,

    #[meta(name = "get_slice", stack_args = 0, immediates = 0, returns = 0)]
    GetSlice = 13, // TODO

    #[meta(name = "call", stack_args = 0, immediates = 1, returns = 1)]
    Call = 14,

    #[meta(name = "==", stack_args = 2, immediates = 0, returns = 1)]
    Equals = 15,

    #[meta(name = "!=", stack_args = 2, immediates = 0, returns = 1)]
    NotEquals = 16,

    #[meta(name = "<", stack_args = 2, immediates = 0, returns = 1)]
    LessThan = 17,

    #[meta(name = "<=", stack_args = 2, immediates = 0, returns = 1)]
    LessThanOrEquals = 18,

    #[meta(name = ">", stack_args = 2, immediates = 0, returns = 1)]
    GreaterThan = 19,

    #[meta(name = ">=", stack_args = 2, immediates = 0, returns = 1)]
    GreaterThanOrEquals = 20,

    #[meta(name = "!", stack_args = 1, immediates = 0, returns = 1)]
    Not = 21,

    #[meta(name = "&&", stack_args = 2, immediates = 0, returns = 1)]
    And = 22,

    #[meta(name = "||", stack_args = 2, immediates = 0, returns = 1)]
    Or = 23,

    #[meta(name = "has", stack_args = 2, immediates = 0, returns = 1)]
    Has = 24,

    #[meta(name = "has_i", stack_args = 2, immediates = 0, returns = 1)]
    HasInsensitive = 25,

    #[meta(name = "matches", stack_args = 2, immediates = 0, returns = 1)]
    Matches = 26,

    #[meta(name = "matches_i", stack_args = 2, immediates = 0, returns = 1)]
    MatchesInsensitive = 27,

    #[meta(name = "+", stack_args = 2, immediates = 0, returns = 1)]
    Add = 28,

    #[meta(name = "-", stack_args = 2, immediates = 0, returns = 1)]
    Subtract = 29,

    #[meta(name = "*", stack_args = 2, immediates = 0, returns = 1)]
    Multiply = 30,

    #[meta(name = "/", stack_args = 2, immediates = 0, returns = 1)]
    Divide = 31,

    #[meta(name = "%", stack_args = 2, immediates = 0, returns = 1)]
    Modulo = 32,

    #[meta(name = "literal_int", stack_args = 0, immediates = 1, returns = 1)]
    LiteralInt = 33,

    #[meta(name = "literal_string", stack_args = 0, immediates = 1, returns = 1)]
    LiteralString = 34,

    #[meta(name = "exit", stack_args = 0, immediates = 0, returns = 0)]
    Exit = 250,
    // TODO: bitwise instructions
    // TODO: custom functions
}

impl Opcode {
    pub fn code(&self) -> u8 {
        self.clone() as u8
    }
}
