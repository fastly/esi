use crate::compiler_types::*;
use crate::opcodes::*;
use crate::parser_types::*;
use bytes::{BufMut, Bytes, BytesMut};
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;

// table of reqref - reqref can be a constant index into a table, it never ends up in a variable

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
}
impl Program<'_> {
    fn new() -> Self {
        Self {
            last_block: None,
            blocks: BlockMap::new(),
            instructions: InstructionMap::new(),
            values: ValueMap::new(),
            inst_values: HashMap::new(),
            requests: 0,
            variables: HashMap::new(),
            data: Vec::new(),
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

    pub fn serialize(&self) -> Bytes {
        let mut symbols = SymbolTable::new();
        let mut relocations = RelocationTable::new();

        let mut buf: OutputBuffer = OutputBuffer::new(BytesMut::new());
        buf.put_u32_le(0xABADBABA); // Magic
        buf.put_u32_le(0x00000001); // Version
        buf.put_u64_le(0); // Length of signature+bytecode segment
        buf.put_u64_le(0); // Length of data segment
        buf.put_u32_le(self.requests); // Variable count
        buf.put_u32_le(self.variables.len() as u32); // Request count

        // Signature + Bytecode segment starts here
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
                data_index as u32, // TODO: why is this a usize rn
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

pub fn generate(ast: Ast) -> Program {
    let mut program = Program::new();
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

                let inst = generate_for_expr(block, subkey, program);
                let subkey_value = program.value_for_inst(inst).unwrap();

                let inst = generate_for_expr(block, expression, program);
                let new_value = program.value_for_inst(inst).unwrap();

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
        Expr::String(s) => program.push_inst(
            block,
            InstBuilder::literal_string(s.unwrap_or("").to_string()),
        ),
        Expr::Variable(key, subkey, default) => {
            let varid: VarId = program.varid(key.to_string());
            let mut value = program.push_inst(block, InstBuilder::get(varid));

            if let Some(subkey) = subkey {
                let subkey_value = generate_for_expr(block, *subkey, program);
                value = program.push_inst(block, InstBuilder::get_key(value, subkey_value));
            }

            if let Some(default) = default {
                let default_value = generate_for_expr(block, *default, program);
                value = program.push_inst(block, InstBuilder::or(value, default_value));
            }

            value
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
        Expr::Call(_, _) => todo!(),
    };
    program.value_for_inst(last_inst).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
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
        println!("{:#?}", ast);

        let program = generate(ast);
        println!("{}", program);
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
        let mut program = Program::new();

        let simple_block = program.new_block();
        generate_for_chunk(
            simple_block,
            Chunk::Esi(Tag::Include(vec![Expr::String(Some("/foo"))])),
            &mut program,
        );

        let expression_block = program.new_block();
        generate_for_chunk(
            expression_block,
            Chunk::Esi(Tag::Include(vec![
                Expr::String(Some("/foo")),
                Expr::Variable("bar", None, None),
                Expr::String(Some("baz")),
            ])),
            &mut program,
        );

        println!("{:#?}", program);

        println!("Simple Include");
        for inst in &program.get_block(simple_block).instructions {
            println!("{:?}", program.get_instruction(*inst));
        }

        println!("Expression Include");
        for inst in &program.get_block(expression_block).instructions {
            println!("{:?}", program.get_instruction(*inst));
        }

        // assert_eq!(
        //     program.last_block().instructions,
        //     [
        //         Instruction::Literal {
        //             value: Value::String("/foo".to_string())
        //         },
        //         Instruction::Request { reqid: 0 },
        //         Instruction::WriteResponse { reqid: 0 },
        //         //
        //         Instruction::Literal {
        //             value: Value::String("/foo".to_string())
        //         },
        //         Instruction::Get { varid: 0 },
        //         Instruction::Add,
        //         Instruction::Literal {
        //             value: Value::String("baz".to_string())
        //         },
        //         Instruction::Add,
        //         Instruction::Request { reqid: 1 },
        //         Instruction::WriteResponse { reqid: 1 },
        //     ]
        // );
    }

    // #[test]
    // fn test_compile_assign_short() {
    //     let mut program = Program::new();
    //     generate_for_chunk(
    //         Chunk::Esi(Tag::Assign(
    //             "test",
    //             None,
    //             Expr::String(Some("this is a string")),
    //         )),
    //         &mut program,
    //     );
    //     generate_for_chunk(
    //         Chunk::Esi(Tag::Assign(
    //             "test",
    //             Some(Expr::String(Some("subkey"))),
    //             Expr::String(Some("this is a string")),
    //         )),
    //         &mut program,
    //     );

    //     println!("{:#?}", program);

    //     assert_eq!(
    //         program.last_block().instructions,
    //         [
    //             Instruction::Literal {
    //                 value: Value::String("this is a string".to_string())
    //             },
    //             Instruction::Set { varid: 0 },
    //             //
    //             Instruction::Get { varid: 0 },
    //             Instruction::Literal {
    //                 value: Value::String("subkey".to_string()),
    //             },
    //             Instruction::Literal {
    //                 value: Value::String("this is a string".to_string())
    //             },
    //             Instruction::SetKey,
    //         ]
    //     );
    // }

    // #[test]
    // fn test_compile_expr_integer() {
    //     let mut program = Program::new();
    //     generate_for_expr(Expr::Integer(0), &mut program);
    //     generate_for_expr(Expr::Integer(1), &mut program);
    //     generate_for_expr(Expr::Integer(i32::MAX), &mut program);
    //     generate_for_expr(Expr::Integer(i32::MIN), &mut program);
    //     println!("{:#?}", &mut program);

    //     assert_eq!(
    //         program.last_block().instructions,
    //         [
    //             Instruction::Literal {
    //                 value: Value::Integer(0)
    //             },
    //             Instruction::Literal {
    //                 value: Value::Integer(1)
    //             },
    //             Instruction::Literal {
    //                 value: Value::Integer(i32::MAX)
    //             },
    //             Instruction::Literal {
    //                 value: Value::Integer(i32::MIN)
    //             }
    //         ]
    //     );
    // }
    // #[test]
    // fn test_compile_expr_string() {
    //     let mut program = Program::new();
    //     generate_for_expr(Expr::String(None), &mut program);
    //     generate_for_expr(Expr::String(Some("")), &mut program);
    //     generate_for_expr(Expr::String(Some("abcdefg")), &mut program);
    //     println!("{:#?}", &mut program);

    //     assert_eq!(
    //         program.last_block().instructions,
    //         [
    //             Instruction::Literal {
    //                 value: Value::String("".to_string())
    //             },
    //             Instruction::Literal {
    //                 value: Value::String("".to_string())
    //             },
    //             Instruction::Literal {
    //                 value: Value::String("abcdefg".to_string())
    //             },
    //         ]
    //     );
    // }
    // #[test]
    // fn test_compile_expr_variable() {
    //     let mut program = Program::new();
    //     generate_for_expr(Expr::Variable("test", None, None), &mut program);
    //     generate_for_expr(
    //         Expr::Variable("test", Some(Box::new(Expr::String(Some("subkey")))), None),
    //         &mut program,
    //     );
    //     generate_for_expr(
    //         Expr::Variable("test", None, Some(Box::new(Expr::Integer(1)))),
    //         &mut program,
    //     );
    //     generate_for_expr(
    //         Expr::Variable(
    //             "test",
    //             Some(Box::new(Expr::String(Some("subkey")))),
    //             Some(Box::new(Expr::Integer(1))),
    //         ),
    //         &mut program,
    //     );

    //     assert_eq!(
    //         program.last_block().instructions,
    //         [
    //             Instruction::Get { varid: 0 },
    //             //
    //             Instruction::Get { varid: 0 },
    //             Instruction::Literal {
    //                 value: Value::String("subkey".to_string())
    //             },
    //             Instruction::GetKey,
    //             //
    //             Instruction::Get { varid: 0 },
    //             Instruction::Literal {
    //                 value: Value::Integer(1)
    //             },
    //             Instruction::Or,
    //             //
    //             Instruction::Get { varid: 0 },
    //             Instruction::Literal {
    //                 value: Value::String("subkey".to_string())
    //             },
    //             Instruction::GetKey,
    //             Instruction::Literal {
    //                 value: Value::Integer(1)
    //             },
    //             Instruction::Or,
    //         ]
    //     );
    // }
    // // #[test]
    // // fn test_compile_expr_call() {
    // //     let mut program = Program::new();
    // //     generate_for_expr(&Expr::Call("function", vec![]), &mut program);
    // //     println!("{:#?}", &mut program);

    // //     assert_eq!(
    // //         program.last_block().instructions,
    // //         [Instruction::Call { varid: 0 },]
    // //     );
    // // }

    // #[test]
    // fn test_compile_expr_comparison() {
    //     let mut program = Program::new();
    //     generate_for_expr(
    //         Expr::Binary {
    //             left: Box::new(Expr::Variable("test", None, None)),
    //             operator: Operator::Matches,
    //             right: Box::new(Expr::String(Some("my-regex"))),
    //         },
    //         &mut program,
    //     );
    //     generate_for_expr(
    //         Expr::Binary {
    //             left: Box::new(Expr::Variable("test2", None, None)),
    //             operator: Operator::Subtract,
    //             right: Box::new(Expr::Integer(1)),
    //         },
    //         &mut program,
    //     );
    //     generate_for_expr(
    //         Expr::Binary {
    //             left: Box::new(Expr::Integer(1)),
    //             operator: Operator::Multiply,
    //             right: Box::new(Expr::Integer(2)),
    //         },
    //         &mut program,
    //     );
    //     generate_for_expr(
    //         Expr::Binary {
    //             left: Box::new(Expr::String(Some("a"))),
    //             operator: Operator::Add,
    //             right: Box::new(Expr::String(Some("b"))),
    //         },
    //         &mut program,
    //     );
    //     println!("{:#?}", &mut program);

    //     assert_eq!(
    //         program.last_block().instructions,
    //         [
    //             Instruction::Get { varid: 0 },
    //             Instruction::Literal {
    //                 value: Value::String("my-regex".to_string())
    //             },
    //             Instruction::Matches,
    //             //--
    //             Instruction::Get { varid: 1 },
    //             Instruction::Literal {
    //                 value: Value::Integer(1),
    //             },
    //             Instruction::Subtract,
    //             //--
    //             Instruction::Literal {
    //                 value: Value::Integer(1),
    //             },
    //             Instruction::Literal {
    //                 value: Value::Integer(2),
    //             },
    //             Instruction::Multiply,
    //             //--
    //             Instruction::Literal {
    //                 value: Value::String("a".to_string())
    //             },
    //             Instruction::Literal {
    //                 value: Value::String("b".to_string())
    //             },
    //             Instruction::Add,
    //         ]
    //     );
    // }

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
        let program = generate(ast);
        println!("{}", program);
        let mut buf = program.serialize();
        println!("{:?}", buf);

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
