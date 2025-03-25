use crate::abi::*;
use crate::compiler_types::*;
use crate::opcodes::*;
use crate::parser_types::*;
use bytes::{BufMut, Bytes, BytesMut};
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub struct Program<'a> {
    last_block: Option<Block>,
    blocks: BlockMap,
    instructions: InstructionMap,
    values: ValueMap,
    inst_values: HashMap<Inst, Value>,
    requests: ReqId,
    variables: HashMap<String, VarId>,
    data: Vec<&'a str>,
    abi: &'static Abi<'static>,
}
impl Program<'_> {
    fn new(abi: &'static Abi) -> Self {
        Self {
            last_block: None,
            blocks: BlockMap::new(),
            instructions: InstructionMap::new(),
            values: ValueMap::new(),
            inst_values: HashMap::new(),
            requests: 0,
            variables: HashMap::new(),
            data: Vec::new(),
            abi: abi,
        }
    }

    fn new_block(&mut self) -> Block {
        let block = self.blocks.push(BlockData {
            previous: self.last_block,
            instructions: Vec::new(),
            next: None,
        });
        if let Some(last_block) = self.last_block {
            self.blocks.get_mut(last_block).next = Some(block);
        }

        self.last_block = Some(block);
        block
    }
    fn push_inst(&mut self, block: Block, inst_data: InstructionData) -> Inst {
        inst_data.validate();
        let returns = inst_data.returns();

        let inst = self.instructions.push(inst_data);
        self.blocks.get_mut(block).push_inst(inst);

        if returns > 0 {
            let value = self.values.push(ValueData { source: inst });
            self.inst_values.insert(inst, value);
        }

        inst
    }

    fn value_for_inst(&self, inst: Inst) -> Option<Value> {
        self.inst_values.get(&inst).copied()
    }

    fn varid(&mut self, key: String) -> VarId {
        let next_varid = self.variables.len();
        *self
            .variables
            .entry(key)
            .or_insert_with(|| VarId::try_from(next_varid).unwrap())
    }

    fn get_instruction(&self, inst: Inst) -> &InstructionData {
        self.instructions.get(inst)
    }
    fn get_block(&self, block: Block) -> &BlockData {
        self.blocks.get(block)
    }

    fn block_iter(&self) -> std::iter::Enumerate<std::slice::Iter<'_, BlockData>> {
        self.blocks.iter().enumerate()
    }
    fn block_instructions_iter(&self) -> impl Iterator<Item = Vec<&InstructionData>> {
        self.block_iter().map(move |(_, bd)| {
            bd.instructions
                .iter()
                .map(|i| self.get_instruction(*i))
                .collect()
        })
    }

    pub fn serialize(&self) -> Bytes {
        let mut symbols = SymbolTable::new();
        let mut relocations = RelocationTable::new();

        let mut buf: OutputBuffer = OutputBuffer::new(BytesMut::new());
        buf.put_u32_le(0xABADBABA); // Magic
        buf.put_u32_le(self.abi.version); // Version
        buf.put_u64_le(0); // Length of signature+bytecode segment
        buf.put_u64_le(0); // Length of data segment
        buf.put_u32_le(self.requests); // Variable count
        buf.put_u32_le(self.variables.len() as u32); // Request count

        // Signature + Bytecode segment starts here
        // TODO: implement signatures
        buf.put_u8(0); // Signature Type (0=None, ...)

        let code_offset = buf.position();
        for (block, block_data) in self.block_iter() {
            symbols.add_block(block, buf.position() - code_offset);

            for inst in &block_data.instructions {
                let inst_data = self.get_instruction(*inst);
                inst_data.serialize(&mut buf, &mut relocations);
            }
        }

        // Data segment starts here
        let data_offset = buf.position();
        for (data_index, slice) in self.data.iter().enumerate() {
            let bytes = slice.as_bytes();

            symbols.add_data(
                data_index as u32,
                buf.position() - data_offset,
                bytes.len() as u32,
            );
            buf.put(bytes);
        }

        let end_offset = buf.position();

        let mut buf = buf.bytes();

        // Set code segment length
        buf[8..16].copy_from_slice(&(data_offset as u64 - code_offset as u64).to_le_bytes());

        // Set data segment length
        buf[16..24].copy_from_slice(&(end_offset as u64 - data_offset as u64).to_le_bytes());

        // Do relocations
        for (symbol, loc) in relocations.iter() {
            let dest = symbols.get(symbol);

            match dest {
                SymbolLocation::CodeOffset(offset) => {
                    let loc: usize = *loc as usize;
                    buf[loc..loc + 4].copy_from_slice(&offset.to_le_bytes());
                }
                SymbolLocation::DataLocation(offset, length) => {
                    let loc: usize = *loc as usize;
                    buf[loc..loc + 4].copy_from_slice(&offset.to_le_bytes());
                    buf[loc + 4..loc + 8].copy_from_slice(&length.to_le_bytes());
                }
            }
        }

        buf.freeze()
    }
}

impl fmt::Display for Program<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (block, block_data) in self.block_iter() {
            write!(f, "block-{}:\n", block)?;
            for inst in &block_data.instructions {
                write!(f, "  ");
                let inst_data = self.get_instruction(*inst);
                if inst_data.opcode.returns() > 0 {
                    let valuestr = self
                        .value_for_inst(*inst)
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| "???".to_string());
                    write!(f, "{} <- ", valuestr);
                }
                write!(f, "{}\n", inst_data)?;
            }
            write!(f, "\n");
        }
        Ok(())
    }
}

pub fn generate<'a>(ast: Ast<'a>, abi: &'static Abi<'static>) -> Program<'a> {
    let mut program = Program::new(abi);
    let first_block = program.new_block();
    let Ast(chunks) = ast;

    let mut block = first_block;
    for chunk in chunks {
        block = generate_for_chunk(block, chunk, &mut program);
    }
    program.push_inst(block, InstBuilder::exit());
    program
}

fn generate_for_chunk<'a>(block: Block, chunk: Chunk<'a>, program: &mut Program<'a>) -> Block {
    match chunk {
        Chunk::Html(data) | Chunk::Text(data) => {
            program.data.push(data);
            let idx: u32 = program.data.len() as u32 - 1;
            program.push_inst(block, InstBuilder::write_bytes(idx));
            block
        }
        Chunk::Esi(tag) => generate_for_esi_tag(block, tag, program),
        Chunk::Expr(expr) => {
            let value = generate_for_expr(block, expr, program);
            program.push_inst(block, InstBuilder::write_value(value));
            block
        }
    }
}

fn interpolation_exprs(exprs: Vec<Expr>) -> Expr {
    exprs
        .into_iter()
        .reduce(|acc, e| Expr::Binary {
            left: Box::new(acc),
            operator: Operator::Add,
            right: Box::new(e),
        })
        .unwrap_or(Expr::String(None))
}

fn generate_for_esi_tag<'a>(block: Block, tag: Tag<'a>, program: &mut Program<'a>) -> Block {
    match tag {
        Tag::Include(src) => {
            let reqid = program.requests;
            program.requests += 1;

            let src_interp_expr = interpolation_exprs(src);
            let value = generate_for_expr(block, src_interp_expr, program);
            program.push_inst(block, InstBuilder::request(reqid, value));
            program.push_inst(block, InstBuilder::write_response(reqid));
            block
        }
        Tag::Try(attempts, except) => {
            // TODO: think through the effect of nesting for try. Both nesting the tries themselves
            //       as well as nesting an include statement inside something else. It seems like we
            //       have to be able to reorder the instructions to make every request happen before
            //       any Write. If that's not possible, we can't compile this correctly (as the try
            //       have side effects that can't be rolled back).
            //       For now, we'll just only respect tries that have an include in the root of the
            //       branches.
            let next_bb = program.new_block();
            let mut attempt_makes_no_requests = false;

            for attempt in attempts {
                let mut attempt_bb = program.new_block();
                let mut reqids = Vec::new();

                // look for the includes
                for chunk in attempt {
                    match chunk {
                        Chunk::Esi(Tag::Include(src)) => {
                            let reqid = program.requests;
                            program.requests += 1;

                            reqids.push(reqid);

                            let src_interp_expr = interpolation_exprs(src);
                            let value = generate_for_expr(block, src_interp_expr, program);
                            program.push_inst(block, InstBuilder::request(reqid, value));
                            program.push_inst(attempt_bb, InstBuilder::write_response(reqid));
                        }
                        chunk => {
                            attempt_bb = generate_for_chunk(attempt_bb, chunk, program);
                        }
                    }
                }

                program.push_inst(attempt_bb, InstBuilder::jump(next_bb));

                if reqids.len() == 0 {
                    // handle the case where the attempt has no includes, i.e. always succeeds
                    // no further attempts or except will be codegen'd as they cannot ever be triggered
                    attempt_makes_no_requests = true;
                    break; // bail early
                } else {
                    let inst = program.push_inst(block, InstBuilder::success(reqids));
                    let value = program.value_for_inst(inst).unwrap();
                    program.push_inst(block, InstBuilder::jump_if(attempt_bb, value));
                }
            }

            let mut block = block;
            if let Some(except) = except {
                if !attempt_makes_no_requests {
                    for chunk in except {
                        block = generate_for_chunk(block, chunk, program);
                    }
                }
            }
            program.push_inst(block, InstBuilder::jump(next_bb));

            next_bb
        }
        Tag::Choose(whens, otherwise) => {
            if whens.len() == 0 {
                return block;
            }

            let next_bb = program.new_block();
            for when in whens {
                if let Chunk::Esi(Tag::When(expr, content)) = when {
                    let when_bb = program.new_block();

                    let value = generate_for_expr(block, expr, program);
                    program.push_inst(block, InstBuilder::jump_if(when_bb, value));

                    // write destination block
                    for chunk in content {
                        generate_for_chunk(when_bb, chunk, program);
                    }
                    program.push_inst(when_bb, InstBuilder::jump(next_bb));
                } else {
                    panic!("Expected When tag");
                }
            }

            if let Some(otherwise) = otherwise {
                let otherwise_bb = program.new_block();

                program.push_inst(block, InstBuilder::jump(otherwise_bb));

                // generate otherwise block
                for chunk in otherwise {
                    generate_for_chunk(otherwise_bb, chunk, program);
                }

                program.push_inst(otherwise_bb, InstBuilder::jump(next_bb));
            } else {
                program.push_inst(block, InstBuilder::jump(next_bb));
            }

            next_bb
        }
        Tag::Assign(name, subkey, expression) => {
            let varid: VarId = program.varid(name.to_string());

            if let Some(subkey) = subkey {
                let inst = program.push_inst(block, InstBuilder::get(varid));
                let var_value = program.value_for_inst(inst).unwrap();
                let subkey_value = generate_for_expr(block, subkey, program);
                let new_value = generate_for_expr(block, expression, program);

                program.push_inst(
                    block,
                    InstBuilder::set_key(var_value, subkey_value, new_value),
                );
            } else {
                let value = generate_for_expr(block, expression, program);
                program.push_inst(block, InstBuilder::set(varid, value));
            }
            block
        }

        tag => panic!("unknown esi tag: {:?}", tag),
    }
}

fn generate_for_expr(block: Block, expr: Expr, program: &mut Program) -> Value {
    let last_inst = match expr {
        Expr::Integer(i) => program.push_inst(block, InstBuilder::literal_int(i)),
        Expr::Bool(b) => program.push_inst(block, InstBuilder::literal_bool(b)),
        Expr::String(s) => program.push_inst(
            block,
            InstBuilder::literal_string(s.unwrap_or("").to_string()),
        ),
        Expr::List(exprs) => {
            let values = exprs
                .into_iter()
                .rev()
                .map(|item_expr| generate_for_expr(block, item_expr, program))
                .collect::<Vec<Value>>();

            program.push_inst(block, InstBuilder::make_list(values.len(), values))
        }
        Expr::Variable(key, subkey, default) => {
            let varid: VarId = program.varid(key.to_string());
            let mut inst = program.push_inst(block, InstBuilder::get(varid));

            if let Some(subkey) = subkey {
                let value = program.value_for_inst(inst).unwrap();
                let subkey_value = generate_for_expr(block, *subkey, program);
                inst = program.push_inst(block, InstBuilder::get_key(value, subkey_value));
            }

            if let Some(default) = default {
                let value = program.value_for_inst(inst).unwrap();
                let default_value = generate_for_expr(block, *default, program);
                inst = program.push_inst(block, InstBuilder::or(value, default_value));
            }

            inst
        }
        Expr::Unary { operator, expr } => {
            let value = generate_for_expr(block, *expr, program);
            let opcode = match operator {
                Operator::Not => Opcode::Not,
                _ => panic!("unexpected operator in unary expression: {:?}", operator),
            };
            program.push_inst(
                block,
                InstructionData {
                    opcode: opcode,
                    stack_args: vec![value],
                    immediates: vec![],
                },
            )
        }
        Expr::Binary {
            left,
            operator,
            right,
        } => {
            let left_value = generate_for_expr(block, *left, program);
            let right_value = generate_for_expr(block, *right, program);
            let opcode = match operator {
                Operator::Has => Opcode::Has,
                Operator::HasInsensitive => Opcode::HasInsensitive,
                Operator::Matches => Opcode::Matches,
                Operator::MatchesInsensitive => Opcode::MatchesInsensitive,
                Operator::Equals => Opcode::Equals,
                Operator::NotEquals => Opcode::NotEquals,
                Operator::LessThan => Opcode::LessThan,
                Operator::LessThanOrEquals => Opcode::LessThanOrEquals,
                Operator::GreaterThan => Opcode::GreaterThan,
                Operator::GreaterThanOrEquals => Opcode::GreaterThanOrEquals,
                Operator::And => Opcode::And,
                Operator::Or => Opcode::Or,
                Operator::Subtract => Opcode::Subtract,
                Operator::Add => Opcode::Add,
                Operator::Divide => Opcode::Divide,
                Operator::Multiply => Opcode::Multiply,
                Operator::Modulo => Opcode::Modulo,
                _ => panic!("unexpected operator in binary expression: {:?}", operator),
            };
            program.push_inst(
                block,
                InstructionData {
                    opcode: opcode,
                    stack_args: vec![left_value, right_value],
                    immediates: vec![],
                },
            )
        }
        Expr::Call(fn_name, arg_exprs) => {
            // TODO: error prop
            let (fn_id, fn_sig) = program.abi.function_by_name(fn_name).unwrap();

            match &fn_sig.args {
                Args::Constant(arg_count) => assert!(*arg_count == arg_exprs.len()),
                Args::Variadic => {}
            }

            let arg_values = arg_exprs
                .into_iter()
                .rev()
                .map(|item_expr| generate_for_expr(block, item_expr, program))
                .collect::<Vec<Value>>();

            program.push_inst(block, InstBuilder::call(fn_id, arg_values))
        }
    };
    program.value_for_inst(last_inst).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abi::ABI_TEST;
    use crate::new_parse::parse_document;
    use bytes::Buf;

    //     #[test]
    //     fn test_compile() {
    //         let input = r#"
    // <a>foo</a>
    // <bar />
    // baz
    // <esi:vars name="$(hello)">
    // <esi:vars>
    // hello <br>
    // </esi:vars>
    // <sCripT src="whatever">
    // <baz>
    // <script> less < more </script>
    // <esi:remove>should not appear</esi:remove>
    // <esi:comment text="also should not appear" />
    // <esi:text> this <esi:vars>$(should)</esi> appear unchanged</esi:text>
    // <esi:include src="whatever" />
    // <esi:choose>
    // should not appear
    // </esi:choose>
    // <esi:choose>
    // should not appear
    // <esi:when test="$(whatever)">hi</esi:when>
    // <esi:otherwise>goodbye</esi:otherwise>
    // should not appear
    // </esi:choose>
    // <esi:try>
    // should not appear
    // <esi:attempt>
    // attempt 1
    // <esi:include src="/attempt1">
    // </esi:attempt>
    // should not appear
    // <esi:attempt>
    // attempt 2
    // <esi:include src="/attempt2">
    // </esi:attempt>
    // should not appear
    // <esi:except>
    // exception!
    // </esi:except>
    // </esi:try>"#;

    //         let ast = parse_document(input).unwrap();

    //         let program = generate(ast);
    //         println!("{:#?}", program);
    //     }

    #[test]
    fn test_compile_try() {
        let input = r#"
    <esi:assign name="foo" value="1">
    <esi:try>
      should not appear
      <esi:attempt>
        attempt 1
        <esi:include src="/attempt1$(foo)">
      </esi:attempt>
      should not appear
      <esi:attempt>
        attempt 2
        <esi:include src="/attempt2a">
        <esi:include src="/attempt2b">
      </esi:attempt>
      should not appear
      <esi:except>
        exception!
      </esi:except>
    </esi:try>"#;

        let ast = parse_document(input).unwrap();
        let program = generate(ast, &ABI_TEST);
    }

    //     #[test]
    //     fn test_compile_try_without_include() {
    //         let input = r#"
    // <esi:try>
    // <esi:attempt>
    // <esi:include src="/should-appear">
    // </esi:attempt>
    // <esi:attempt>
    // cannot fail
    // </esi:attempt>
    // <esi:attempt>
    // <esi:include src="/should-not-appear">
    // </esi:attempt>
    // <esi:except>
    // <esi:include src="/should-not-appear-either">
    // </esi:except>
    // </esi:try>"#;
    //         let ast = parse_document(input).unwrap();

    //         let program = generate(ast);
    //         println!("{:#?}", program);
    //     }

    #[test]
    fn test_compile_include() {
        let program = generate(
            Ast(vec![Chunk::Esi(Tag::Include(vec![
                Expr::String(Some("/foo/")),
                Expr::Variable("bar", None, None),
                Expr::String(Some("?whatever")),
            ]))]),
            &ABI_TEST,
        );

        let blocks: Vec<Vec<&InstructionData>> = program.block_instructions_iter().collect();
        let instructions = &blocks[0];

        assert_eq!(
            &instructions[0..7],
            &vec![
                &InstBuilder::literal_string("/foo/".to_string()),
                &InstBuilder::get(0),
                &InstructionData {
                    opcode: Opcode::Add,
                    stack_args: vec![0, 1],
                    immediates: vec![],
                },
                &InstBuilder::literal_string("?whatever".to_string()),
                &InstructionData {
                    opcode: Opcode::Add,
                    stack_args: vec![2, 3],
                    immediates: vec![],
                },
                &InstBuilder::request(0, 4),
                &InstBuilder::write_response(0),
            ]
        );
    }

    #[test]
    fn test_compile_assign_short() {
        let program = generate(
            Ast(vec![
                Chunk::Esi(Tag::Assign(
                    "test",
                    None,
                    Expr::String(Some("this is a string")),
                )),
                Chunk::Esi(Tag::Assign(
                    "test",
                    Some(Expr::String(Some("subkey"))),
                    Expr::String(Some("this is a string")),
                )),
            ]),
            &ABI_TEST,
        );

        let blocks: Vec<Vec<&InstructionData>> = program.block_instructions_iter().collect();
        let instructions = &blocks[0];

        assert_eq!(
            &instructions[0..2],
            &vec![
                &InstBuilder::literal_string("this is a string".to_string()),
                &InstBuilder::set(0, 0),
            ]
        );
        assert_eq!(
            &instructions[2..6],
            &vec![
                &InstBuilder::get(0),
                &InstBuilder::literal_string("subkey".to_string()),
                &InstBuilder::literal_string("this is a string".to_string()),
                &InstBuilder::set_key(1, 2, 3),
            ]
        );
    }

    #[test]
    fn test_compile_expr_integer() {
        let program = generate(
            Ast(vec![
                Chunk::Expr(Expr::Integer(0)),
                Chunk::Expr(Expr::Integer(1)),
                Chunk::Expr(Expr::Integer(i32::MAX)),
                Chunk::Expr(Expr::Integer(i32::MIN)),
            ]),
            &ABI_TEST,
        );

        let blocks: Vec<Vec<&InstructionData>> = program.block_instructions_iter().collect();
        let instructions = &blocks[0];

        assert_eq!(
            &instructions[0..8],
            &vec![
                &InstBuilder::literal_int(0),
                &InstBuilder::write_value(0),
                &InstBuilder::literal_int(1),
                &InstBuilder::write_value(1),
                &InstBuilder::literal_int(i32::MAX),
                &InstBuilder::write_value(2),
                &InstBuilder::literal_int(i32::MIN),
                &InstBuilder::write_value(3),
            ]
        );
    }
    #[test]
    fn test_compile_expr_variable() {
        let program = generate(
            Ast(vec![
                Chunk::Expr(Expr::Variable("test", None, None)),
                Chunk::Expr(Expr::Variable(
                    "test",
                    Some(Box::new(Expr::String(Some("subkey")))),
                    None,
                )),
                Chunk::Expr(Expr::Variable(
                    "test",
                    None,
                    Some(Box::new(Expr::Integer(1))),
                )),
                Chunk::Expr(Expr::Variable(
                    "test",
                    Some(Box::new(Expr::String(Some("subkey")))),
                    Some(Box::new(Expr::Integer(1))),
                )),
            ]),
            &ABI_TEST,
        );

        let blocks: Vec<Vec<&InstructionData>> = program.block_instructions_iter().collect();
        let instructions = &blocks[0];

        assert_eq!(&instructions[0..1], &vec![&InstBuilder::get(0)]);
        assert_eq!(
            &instructions[2..5],
            &vec![
                &InstBuilder::get(0),
                &InstBuilder::literal_string("subkey".to_string()),
                &InstBuilder::get_key(1, 2),
            ]
        );
        assert_eq!(
            &instructions[6..9],
            &vec![
                &InstBuilder::get(0),
                &InstBuilder::literal_int(1),
                &InstBuilder::or(4, 5),
            ]
        );
        assert_eq!(
            &instructions[10..15],
            &vec![
                &InstBuilder::get(0),
                &InstBuilder::literal_string("subkey".to_string()),
                &InstBuilder::get_key(7, 8),
                &InstBuilder::literal_int(1),
                &InstBuilder::or(9, 10),
            ]
        );
    }

    #[test]
    fn test_compile_expr_string() {
        let program = generate(
            Ast(vec![
                Chunk::Expr(Expr::String(None)),
                Chunk::Expr(Expr::String(Some(""))),
                Chunk::Expr(Expr::String(Some("abcdefg"))),
            ]),
            &ABI_TEST,
        );

        let blocks: Vec<Vec<&InstructionData>> = program.block_instructions_iter().collect();
        let instructions = &blocks[0];

        assert_eq!(
            &instructions[0..6],
            &vec![
                &InstBuilder::literal_string("".to_string()),
                &InstBuilder::write_value(0),
                &InstBuilder::literal_string("".to_string()),
                &InstBuilder::write_value(1),
                &InstBuilder::literal_string("abcdefg".to_string()),
                &InstBuilder::write_value(2),
            ]
        );
    }

    #[test]
    fn test_compile_expr_list() {
        let program = generate(
            Ast(vec![Chunk::Expr(Expr::List(vec![
                Expr::String(None),
                Expr::String(Some("")),
                Expr::String(Some("abcdefg")),
            ]))]),
            &ABI_TEST,
        );

        let blocks: Vec<Vec<&InstructionData>> = program.block_instructions_iter().collect();
        let instructions = &blocks[0];

        assert_eq!(
            &instructions[0..4],
            &vec![
                &InstBuilder::literal_string("abcdefg".to_string()),
                &InstBuilder::literal_string("".to_string()),
                &InstBuilder::literal_string("".to_string()),
                &InstBuilder::make_list(3, vec![0, 1, 2]),
            ]
        );
    }

    #[test]
    fn test_compile_expr_unary() {
        let program = generate(
            Ast(vec![Chunk::Expr(Expr::Unary {
                operator: Operator::Not,
                expr: Box::new(Expr::Integer(1)),
            })]),
            &ABI_TEST,
        );

        let blocks: Vec<Vec<&InstructionData>> = program.block_instructions_iter().collect();
        let instructions = &blocks[0];

        assert_eq!(
            &instructions[0..2],
            &vec![
                &InstBuilder::literal_int(1),
                &InstructionData {
                    opcode: Opcode::Not,
                    stack_args: vec![0],
                    immediates: vec![]
                },
            ]
        );
    }

    #[test]
    fn test_compile_expr_binary() {
        let program = generate(
            Ast(vec![
                Chunk::Expr(Expr::Binary {
                    left: Box::new(Expr::Variable("test", None, None)),
                    operator: Operator::Matches,
                    right: Box::new(Expr::String(Some("my-regex"))),
                }),
                Chunk::Expr(Expr::Binary {
                    left: Box::new(Expr::Variable("test2", None, None)),
                    operator: Operator::Subtract,
                    right: Box::new(Expr::Integer(1)),
                }),
                Chunk::Expr(Expr::Binary {
                    left: Box::new(Expr::Integer(1)),
                    operator: Operator::Multiply,
                    right: Box::new(Expr::Integer(2)),
                }),
                Chunk::Expr(Expr::Binary {
                    left: Box::new(Expr::String(Some("a"))),
                    operator: Operator::Add,
                    right: Box::new(Expr::String(Some("b"))),
                }),
            ]),
            &ABI_TEST,
        );

        let blocks: Vec<Vec<&InstructionData>> = program.block_instructions_iter().collect();
        let instructions = &blocks[0];

        assert_eq!(
            &instructions[0..3],
            &vec![
                &InstBuilder::get(0),
                &InstBuilder::literal_string("my-regex".to_string()),
                &InstructionData {
                    opcode: Opcode::Matches,
                    stack_args: vec![0, 1],
                    immediates: vec![]
                },
            ]
        );

        assert_eq!(
            &instructions[4..7],
            &vec![
                &InstBuilder::get(1),
                &InstBuilder::literal_int(1),
                &InstructionData {
                    opcode: Opcode::Subtract,
                    stack_args: vec![3, 4],
                    immediates: vec![]
                },
            ]
        );

        assert_eq!(
            &instructions[8..11],
            &vec![
                &InstBuilder::literal_int(1),
                &InstBuilder::literal_int(2),
                &InstructionData {
                    opcode: Opcode::Multiply,
                    stack_args: vec![6, 7],
                    immediates: vec![]
                },
            ]
        );

        assert_eq!(
            &instructions[12..15],
            &vec![
                &InstBuilder::literal_string("a".to_string()),
                &InstBuilder::literal_string("b".to_string()),
                &InstructionData {
                    opcode: Opcode::Add,
                    stack_args: vec![9, 10],
                    immediates: vec![]
                },
            ]
        );
    }

    #[test]
    fn test_compile_expr_call() {
        let program = generate(
            Ast(vec![
                Chunk::Expr(Expr::Call("ping", vec![])),
                Chunk::Expr(Expr::Call("identity", vec![Expr::Integer(1)])),
            ]),
            &ABI_TEST,
        );

        let blocks: Vec<Vec<&InstructionData>> = program.block_instructions_iter().collect();
        let instructions = &blocks[0];

        assert_eq!(&instructions[0..1], &vec![&InstBuilder::call(0, vec![]),]);
        assert_eq!(
            &instructions[2..4],
            &vec![&InstBuilder::literal_int(1), &InstBuilder::call(1, vec![1]),]
        );
    }

    // #[test]
    // fn test_compile_expr_output() {
    //     let mut program = Program::new();
    //     let chunk = Chunk::Expr(Expr::Binary {
    //         left: Box::new(Expr::String(Some("hello "))),
    //         operator: Operator::Add,
    //         right: Box::new(Expr::String(Some("world!"))),
    //     });

    //     generate_for_chunk(chunk, &mut program);

    //     println!("{:#?}", program);
    // }

    #[test]
    fn test_serialize() {
        let input = r#"
    <esi:assign name="foo" value="1">
    <esi:try>
      should not appear
      <esi:attempt>
        attempt 1
        <esi:include src="/attempt1$(foo)">
      </esi:attempt>
      should not appear
      <esi:attempt>
        attempt 2
        <esi:include src="/attempt2a">
        <esi:include src="/attempt2b">
      </esi:attempt>
      should not appear
      <esi:except>
        exception!
      </esi:except>
    </esi:try>"#;

        let ast = parse_document(input).unwrap();
        let program = generate(ast, &ABI_TEST);
        let mut buf = program.serialize();

        // Header
        assert_eq!(0xABADBABA, buf.get_u32());
        assert_eq!(0x00000001, buf.get_u32());
        assert_eq!(210, buf.get_u64()); // Code segment length
        assert_eq!(113, buf.get_u64()); // Data segment length
        assert_eq!(0, buf.get_u8());

        assert_eq!(Opcode::WriteBytes.code(), buf.get_u8()); // write_bytes opcode
        assert_eq!(0, buf.get_u32()); // offset
        assert_eq!(5, buf.get_u32()); // length

        assert_eq!(Opcode::LiteralInt.code(), buf.get_u8()); // literal_int opcode
        assert_eq!(1, buf.get_u32()); // integer 1

        assert_eq!(Opcode::Set.code(), buf.get_u8()); // set opcode
        assert_eq!(0, buf.get_u32()); // var 0

        assert_eq!(Opcode::WriteBytes.code(), buf.get_u8()); // write_bytes opcode
        assert_eq!(5, buf.get_u32()); // offset
        assert_eq!(5, buf.get_u32()); // length

        assert_eq!(Opcode::LiteralString.code(), buf.get_u8()); // literal_string opcode
        assert_eq!(9, buf.get_u32()); // length
        let mut litstr = [0; 9];
        buf.copy_to_slice(&mut litstr);
        assert_eq!(b"/attempt1", &litstr); // string "/attempt1"

        assert_eq!(Opcode::Get.code(), buf.get_u8()); // get opcode
        assert_eq!(0, buf.get_u32()); // var 0

        assert_eq!(Opcode::Add.code(), buf.get_u8()); // + opcode

        assert_eq!(Opcode::Request.code(), buf.get_u8()); // request opcode
        assert_eq!(0, buf.get_u32()); // req 0

        assert_eq!(Opcode::Success.code(), buf.get_u8()); // success opcode
        assert_eq!(1, buf.get_u32()); // length of req list
        assert_eq!(0, buf.get_u32()); // req 0

        assert_eq!(Opcode::JumpIf.code(), buf.get_u8()); // jump_if opcode
        assert_eq!(140, buf.get_u32()); // block:2 address

        assert_eq!(Opcode::LiteralString.code(), buf.get_u8()); // literal_string opcode
        assert_eq!(10, buf.get_u32()); // length
        let mut litstr = [0; 10];
        buf.copy_to_slice(&mut litstr);
        assert_eq!(b"/attempt2a", &litstr); // string "/attempt2a"

        assert_eq!(Opcode::Request.code(), buf.get_u8()); // request opcode
        assert_eq!(1, buf.get_u32()); // req 1

        assert_eq!(Opcode::LiteralString.code(), buf.get_u8()); // literal_string opcode
        assert_eq!(10, buf.get_u32()); // length
        let mut litstr = [0; 10];
        buf.copy_to_slice(&mut litstr);
        assert_eq!(b"/attempt2b", &litstr); // string "/attempt2b"

        assert_eq!(Opcode::Request.code(), buf.get_u8()); // request opcode
        assert_eq!(2, buf.get_u32()); // req 2

        assert_eq!(Opcode::Success.code(), buf.get_u8()); // success opcode
        assert_eq!(2, buf.get_u32()); // length of req list
        assert_eq!(1, buf.get_u32()); // req 1
        assert_eq!(2, buf.get_u32()); // req 2

        assert_eq!(Opcode::JumpIf.code(), buf.get_u8()); // jump_if opcode
        assert_eq!(168, buf.get_u32()); // block:3 address

        assert_eq!(Opcode::WriteBytes.code(), buf.get_u8()); // write_bytes opcode
        assert_eq!(87, buf.get_u32()); // offset
        assert_eq!(26, buf.get_u32()); // length

        assert_eq!(Opcode::Jump.code(), buf.get_u8()); // jump opcode
        assert_eq!(139, buf.get_u32()); // block:1 address

        // beginning of block-1
        assert_eq!(Opcode::Exit.code(), buf.get_u8()); // exit opcode

        // beginning of block-2
    }
}
