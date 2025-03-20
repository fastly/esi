use crate::opcodes::*;
use bytes::buf::UninitSlice;
use bytes::{BufMut, BytesMut};
use std::collections::HashMap;
use std::convert::TryInto;
use std::fmt;
use std::marker::PhantomData;
use std::slice::{Iter, SliceIndex};

#[derive(Debug, Clone, PartialEq)]
pub struct EntityMap<K, V>(Vec<V>, PhantomData<K>);
impl<K: SliceIndex<[V], Output = V> + From<usize>, V> EntityMap<K, V> {
    pub fn new() -> Self {
        Self(Vec::new(), PhantomData)
    }
    pub fn get(&self, k: K) -> &V {
        self.0.get(k).unwrap()
    }
    pub fn get_mut(&mut self, k: K) -> &mut V {
        self.0.get_mut(k).unwrap()
    }
    pub fn push(&mut self, v: V) -> K {
        let k: K = self.0.len().into();
        self.0.push(v);
        k
    }
    pub fn iter(&self) -> Iter<'_, V> {
        self.0.iter()
    }
}

// struct OpcodeInfo {
//     arguments: usize,
//     immediates: usize,
//     has_return: bool,
//     is_jump: bool,
// }
// const OPCODE_INFO: [OpcodeInfo] = {
pub type VarId = u32;
pub type ReqId = u32;
pub type MetaVarId = u32;
pub type FunctionId = u32;
pub type DataIndex = u32;

#[repr(u8)]
#[derive(Debug, Clone, PartialEq)]
pub enum Immediate {
    DataIndex(DataIndex),
    ReqId(ReqId),
    ReqIdList(Vec<ReqId>),
    VarId(VarId),
    MetaVarId(MetaVarId),
    FunctionId(FunctionId),
    Location(Block),
    Integer(i32),
    String(String),
    Boolean(bool),
    Null,
}

impl Immediate {
    pub fn type_code(&self) -> u8 {
        unsafe { *(self as *const Self as *const u8) }
    }

    pub fn serialize(&self, buf: &mut OutputBuffer, relocations: &mut RelocationTable) {
        match self {
            Immediate::DataIndex(idx) => {
                relocations.add_data_ref(*idx, buf.position());
                buf.put_u32_le(0); // Offset
                buf.put_u32_le(0); // Length
            }
            Immediate::ReqId(req_id) => {
                buf.put_u32_le(*req_id);
            }
            Immediate::ReqIdList(reqid_list) => {
                buf.put_u16_le(reqid_list.len().try_into().unwrap());
                for req_id in reqid_list {
                    buf.put_u32_le(*req_id);
                }
            }
            Immediate::VarId(var_id) => {
                buf.put_u32_le(*var_id);
            }

            Immediate::MetaVarId(meta_var_id) => {
                buf.put_u32_le(*meta_var_id);
            }
            Immediate::FunctionId(func_id) => {
                buf.put_u32_le(*func_id);
            }
            Immediate::Location(block) => {
                relocations.add_block_ref(*block, buf.position());
                buf.put_u32_le(0);
            }
            Immediate::Integer(n) => {
                buf.put_i32_le(*n);
            }
            Immediate::String(s) => {
                // TODO: I hate this. Add a string relocation thingie.
                let bytestring = s.as_bytes();
                buf.put_u32_le(bytestring.len() as u32);
                buf.put(bytestring);
            }
            Immediate::Boolean(b) => {
                let bool_byte: u8 = if *b { 1 } else { 0 };
                buf.put_u8(bool_byte);
            }
            Immediate::Null => {}
        }
    }
}
impl fmt::Display for Immediate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Immediate::DataIndex(idx) => write!(f, "data-index:{}", idx),
            Immediate::ReqId(req_id) => write!(f, "req:{}", req_id),
            Immediate::ReqIdList(reqid_list) => write!(f, "req-list:{:?}", reqid_list),
            Immediate::VarId(var_id) => write!(f, "var:{}", var_id),
            Immediate::MetaVarId(meta_var_id) => write!(f, "meta-var:{}", meta_var_id),
            Immediate::FunctionId(func_id) => write!(f, "function:{}", func_id),
            Immediate::Location(block) => write!(f, "block:{}", block),
            Immediate::Integer(n) => write!(f, "i{}", n),
            Immediate::String(s) => write!(f, "{:?}", s),
            Immediate::Boolean(b) => write!(f, "{:?}", b),
            Immediate::Null => write!(f, "(null)"),
        }
    }
}

pub type Inst = usize;

pub struct InstBuilder();
impl InstBuilder {
    pub fn write_bytes(idx: DataIndex) -> InstructionData {
        InstructionData {
            opcode: Opcode::WriteBytes,
            stack_args: vec![],
            immediates: vec![Immediate::DataIndex(idx)],
        }
    }
    pub fn write_value(value: Value) -> InstructionData {
        InstructionData {
            opcode: Opcode::WriteValue,
            stack_args: vec![value],
            immediates: vec![],
        }
    }

    pub fn write_response(reqid: ReqId) -> InstructionData {
        InstructionData {
            opcode: Opcode::WriteResponse,
            stack_args: vec![],
            immediates: vec![Immediate::ReqId(reqid)],
        }
    }

    pub fn request(reqid: ReqId, value: Value) -> InstructionData {
        InstructionData {
            opcode: Opcode::Request,
            stack_args: vec![value],
            immediates: vec![Immediate::ReqId(reqid)],
        }
    }

    pub fn success(reqid_list: Vec<ReqId>) -> InstructionData {
        InstructionData {
            opcode: Opcode::Success,
            stack_args: vec![],
            immediates: vec![Immediate::ReqIdList(reqid_list)],
        }
    }

    pub fn jump_if(block: Block, value: Value) -> InstructionData {
        InstructionData {
            opcode: Opcode::JumpIf,
            stack_args: vec![value],
            immediates: vec![Immediate::Location(block)],
        }
    }

    pub fn jump(block: Block) -> InstructionData {
        InstructionData {
            opcode: Opcode::Jump,
            stack_args: vec![],
            immediates: vec![Immediate::Location(block)],
        }
    }

    pub fn get(varid: VarId) -> InstructionData {
        InstructionData {
            opcode: Opcode::Get,
            stack_args: vec![],
            immediates: vec![Immediate::VarId(varid)],
        }
    }
    pub fn set_key(var: Value, subkey: Value, value: Value) -> InstructionData {
        InstructionData {
            opcode: Opcode::SetKey,
            stack_args: vec![var, subkey, value],
            immediates: vec![],
        }
    }

    pub fn set(varid: VarId, value: Value) -> InstructionData {
        InstructionData {
            opcode: Opcode::Set,
            stack_args: vec![value],
            immediates: vec![Immediate::VarId(varid)],
        }
    }

    pub fn literal_int(i: i32) -> InstructionData {
        InstructionData {
            opcode: Opcode::LiteralInt,
            stack_args: vec![],
            immediates: vec![Immediate::Integer(i)],
        }
    }
    pub fn literal_string(s: String) -> InstructionData {
        InstructionData {
            opcode: Opcode::LiteralString,
            stack_args: vec![],
            immediates: vec![Immediate::String(s)],
        }
    }
    pub fn make_list(len: usize, values: Vec<Value>) -> InstructionData {
        InstructionData {
            opcode: Opcode::MakeList,
            stack_args: values,
            immediates: vec![Immediate::Integer(len.try_into().unwrap())],
        }
    }
    pub fn get_key(var: Value, subkey: Value) -> InstructionData {
        InstructionData {
            opcode: Opcode::GetKey,
            stack_args: vec![var, subkey],
            immediates: vec![],
        }
    }

    pub fn or(left: Value, right: Value) -> InstructionData {
        InstructionData {
            opcode: Opcode::Or,
            stack_args: vec![left, right],
            immediates: vec![],
        }
    }
    pub fn exit() -> InstructionData {
        InstructionData {
            opcode: Opcode::Exit,
            stack_args: vec![],
            immediates: vec![],
        }
    }
    pub fn call(func_id: FunctionId, args: Vec<Value>) -> InstructionData {
        let args_len = args.len();
        InstructionData {
            opcode: Opcode::Call,
            stack_args: args,
            immediates: vec![
                Immediate::FunctionId(func_id),
                Immediate::Integer(args_len as i32),
            ],
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct InstructionData {
    pub opcode: Opcode,
    pub stack_args: Vec<Value>,
    pub immediates: Vec<Immediate>,
}
impl InstructionData {
    pub fn validate(&self) {
        if self.opcode.expected_stack_args() != usize::MAX {
            assert_eq!(
                self.opcode.expected_stack_args(),
                self.stack_args.len(),
                "Expected {} stack args for {:?} instruction, but got {}",
                self.opcode.expected_stack_args(),
                self.opcode,
                self.stack_args.len()
            );
        }
        assert_eq!(
            self.opcode.expected_immediates(),
            self.immediates.len(),
            "Expected {} immediates for {:?} instruction, but got {}",
            self.opcode.expected_immediates(),
            self.opcode,
            self.immediates.len()
        );
    }

    pub fn returns(&self) -> usize {
        self.opcode.returns()
    }

    pub fn serialize(&self, buf: &mut OutputBuffer, relocations: &mut RelocationTable) {
        buf.put_u8(self.opcode.code());
        for imm in &self.immediates {
            imm.serialize(buf, relocations);
        }
    }
}

impl fmt::Display for InstructionData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.opcode.name())?;
        if self.opcode.expected_immediates() > 0 {
            let argstr = self
                .immediates
                .iter()
                .cloned()
                .map(|arg| format!("{}", arg))
                .collect::<Vec<String>>()
                .join(", ");
            write!(f, " {}", argstr)?;
        }
        if self.opcode.expected_stack_args() > 0 {
            let argstr = self
                .stack_args
                .iter()
                .cloned()
                .map(|arg| format!("{}", arg))
                .collect::<Vec<String>>()
                .join(", ");
            write!(f, " <- {}", argstr)?;
        }
        Ok(())
    }
}

pub type InstructionMap = EntityMap<Inst, InstructionData>;

pub type Value = usize;
#[derive(Debug, Clone, PartialEq)]
pub struct ValueData {
    pub source: Inst,
}
pub type ValueMap = EntityMap<Value, ValueData>;

pub type Block = usize;
#[derive(Debug, Clone, PartialEq)]
pub struct BlockData {
    pub previous: Option<Block>,
    pub instructions: Vec<Inst>,
    pub next: Option<Block>,
}
impl BlockData {
    pub fn push_inst(&mut self, inst: Inst) {
        self.instructions.push(inst);
    }
}

pub type BlockMap = EntityMap<Block, BlockData>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RelocatableSymbol {
    Block(Block),
    Data(DataIndex),
}

#[derive(Debug, Clone, PartialEq)]
pub enum SymbolLocation {
    CodeOffset(u32),
    DataLocation(u32, u32),
}

#[derive(Debug, Clone, PartialEq)]
pub struct SymbolTable(HashMap<RelocatableSymbol, SymbolLocation>);
impl SymbolTable {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn add_block(&mut self, block: Block, offset: u32) {
        self.0.insert(
            RelocatableSymbol::Block(block),
            SymbolLocation::CodeOffset(offset),
        );
    }

    pub fn add_data(&mut self, data_index: DataIndex, offset: u32, length: u32) {
        self.0.insert(
            RelocatableSymbol::Data(data_index),
            SymbolLocation::DataLocation(offset, length),
        );
    }

    pub fn get(&self, symbol: &RelocatableSymbol) -> &SymbolLocation {
        self.0.get(symbol).unwrap()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RelocationTable(Vec<(RelocatableSymbol, u32)>);
impl RelocationTable {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn add_block_ref(&mut self, block: Block, offset: u32) {
        self.0.push((RelocatableSymbol::Block(block), offset));
    }

    pub fn add_data_ref(&mut self, data_index: DataIndex, offset: u32) {
        self.0.push((RelocatableSymbol::Data(data_index), offset));
    }

    pub fn iter(&self) -> Iter<'_, (RelocatableSymbol, u32)> {
        self.0.iter()
    }
}

pub struct OutputBuffer(u32, BytesMut);
impl OutputBuffer {
    pub fn new(bytes: BytesMut) -> Self {
        Self(0, bytes)
    }
    pub fn position(&self) -> u32 {
        self.0
    }
    pub fn bytes(self) -> BytesMut {
        self.1
    }
}
unsafe impl BufMut for OutputBuffer {
    fn remaining_mut(&self) -> usize {
        self.1.remaining_mut()
    }

    unsafe fn advance_mut(&mut self, cnt: usize) {
        let cnt32: u32 = cnt.try_into().unwrap();
        self.0 += cnt32;
        self.1.advance_mut(cnt);
    }

    fn chunk_mut(&mut self) -> &mut UninitSlice {
        self.1.chunk_mut()
    }
}
