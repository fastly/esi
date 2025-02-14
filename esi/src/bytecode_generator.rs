use crate::parser_types::*;
use std::cell::{RefCell, RefMut};
use std::collections::{HashMap, VecDeque};
use std::convert::TryFrom;
use std::rc::{Rc, Weak};

// table of reqref - reqref can be a constant index into a table, it never ends up in a variable

#[derive(Debug, Clone, PartialEq)]
struct Program {
    blocks: Vec<Rc<RefCell<BasicBlock>>>,
    requests: u32,
    variables: HashMap<String, VarId>,
}
impl Program {
    fn new() -> Self {
        Self {
            blocks: vec![Rc::new(RefCell::new(BasicBlock::new()))],
            requests: 0,
            variables: HashMap::new(),
        }
    }
    fn last_block(&mut self) -> RefMut<'_, BasicBlock> {
        self.blocks.last_mut().unwrap().borrow_mut()
    }
}

#[derive(Debug, Clone, PartialEq)]
struct BasicBlock {
    instructions: Vec<Instruction>,
}
impl BasicBlock {
    fn new() -> Self {
        Self {
            instructions: Vec::new(),
        }
    }
    fn push(&mut self, instruction: Instruction) {
        self.instructions.push(instruction);
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Integer(i32),
    String(String),
    Boolean(bool),
    Null,
}

type ReqId = u32;
type VarId = u32;
type MetaVarId = u32;
type FunctionId = u16;
#[derive(Debug, Clone)]
pub enum Location {
    Block(Weak<RefCell<BasicBlock>>),
    Offset(u32),
}
impl PartialEq for Location {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Self::Block(bb) => match other {
                Self::Block(other_bb) => bb.upgrade() == other_bb.upgrade(),
                Self::Offset(_) => false,
            },
            Self::Offset(offset) => match other {
                Self::Block(_) => false,
                Self::Offset(other_offset) => offset == other_offset,
            },
        }
    }
}

#[repr(u8)]
#[derive(Debug, Clone, PartialEq)]
enum Instruction {
    // (write_bytes start len)
    WriteBytes { start: u64, length: u64 },

    // (request) url
    Request { reqid: ReqId, url: String },

    // (write_response reqid)
    WriteResponse { reqid: ReqId },

    // (success [reqids]) -> bool
    Success { reqids: Vec<ReqId> },

    // (jump location)
    Jump { location: Location },

    // (jump_if location) conditional
    JumpIf { location: Location },

    // (set var) value
    Set { var: VarId },

    // (get var) -> value
    Get { var: VarId },

    // (get_meta metavar) -> value
    GetMeta { metavar: MetaVarId },

    // (set_key) key value
    SetKey,

    // (get_key) key value -> value
    GetKey,

    // (get_slice) start end value -> value
    GetSlice,

    // (call fnid) [args] -> (value)
    Call { function: FunctionId },

    // (==) left right -> value
    Equals,

    // (!=) left right -> value
    NotEquals,

    // (<) left right -> value
    LessThan,

    // (<=) left right -> value
    LessThanOrEquals,

    // (>) left right -> value
    GreaterThan,

    // (>=) left right -> value
    GreaterThanOrEquals,

    // (!) value -> value
    Not,

    // (&&) left right -> value
    And,

    // (||) left right -> value
    Or,

    // (has) haystack needle -> value
    Has,

    // (has_i) haystack needle -> value
    HasInsensitive,

    // (matches) haystack needle -> value
    Matches,

    // (matches_i) haystack needle -> value
    MatchesInsensitive,

    // (+) left right -> value
    Add,

    // (-) left right -> value
    Subtract,

    // (*) left right -> value
    Multiply,

    // (/) left right -> value
    Divide,

    // (%) left right -> value
    Modulo,

    // (literal value) -> value
    Literal { value: Value },
    // TODO: bitwise instructions
    // TODO: custom functions
}
pub fn generate(ast: Ast) -> Program {
    let mut program = Program::new();
    let Ast(chunks) = ast;
    for chunk in chunks {
        generate_for_chunk(&chunk, &mut program);
    }
    program
}

fn generate_for_chunk(chunk: &Chunk, program: &mut Program) {
    match chunk {
        Chunk::Html(data) => program.last_block().push(Instruction::WriteBytes {
            start: 0,
            length: 0,
        }),
        Chunk::Text(data) => program.last_block().push(Instruction::WriteBytes {
            start: 0,
            length: 0,
        }),
        Chunk::Esi(tag) => generate_for_esi_tag(tag, program),
        chunk => println!("unknown chunk: {:?}", chunk),
    }
}

fn generate_for_esi_tag(tag: &Tag, program: &mut Program) {
    match tag {
        Tag::Include(attrs) => match attrs.iter().find(|&&(name, _)| name == "src") {
            None => return,
            Some(&(_, src)) => {
                let reqid = program.requests;
                program.requests += 1;

                let mut current = program.last_block();
                current.push(Instruction::Request {
                    reqid: reqid,
                    url: src.to_owned(),
                });
                current.push(Instruction::WriteResponse { reqid: reqid });
            }
        },
        Tag::Choose(whens, otherwise) => {
            if whens.len() == 0 {
                return;
            }
            let next_bb = Rc::new(RefCell::new(BasicBlock::new()));
            let mut when_bbs = VecDeque::new();
            for when in whens {
                if let Chunk::Esi(Tag::When(expr, _content)) = when {
                    let when_bb = Rc::new(RefCell::new(BasicBlock::new()));

                    generate_for_expr(expr, program);
                    program.last_block().push(Instruction::JumpIf {
                        location: Location::Block(Rc::downgrade(&when_bb)),
                    });

                    when_bbs.push_back(when_bb);
                } else {
                    panic!("Expected When tag");
                }
            }

            if let Some(otherwise) = otherwise {
                let otherwise_bb = Rc::new(RefCell::new(BasicBlock::new()));
                program.last_block().push(Instruction::Jump {
                    location: Location::Block(Rc::downgrade(&otherwise_bb)),
                });

                program.blocks.push(otherwise_bb);
                for chunk in otherwise {
                    generate_for_chunk(chunk, program);
                }
            }
            program.last_block().push(Instruction::Jump {
                location: Location::Block(Rc::downgrade(&next_bb)),
            });

            for when in whens {
                if let Chunk::Esi(Tag::When(_expr, content)) = when {
                    let when_bb = when_bbs.pop_front().unwrap();
                    program.blocks.push(when_bb);
                    for chunk in content {
                        generate_for_chunk(chunk, program);
                    }
                    program.last_block().push(Instruction::Jump {
                        location: Location::Block(Rc::downgrade(&next_bb)),
                    });
                } else {
                    panic!("Expected When tag");
                }
            }

            program.blocks.push(next_bb);
        }
        Tag::Try(attempts, except) => {
            let next_bb = Rc::new(RefCell::new(BasicBlock::new()));
            let mut attempt_no_include = false;

            let mut attempt_contexts = VecDeque::new();
            for attempt in attempts {
                let mut reqids = VecDeque::new();
                // look for the includes
                for chunk in attempt {
                    match chunk {
                        Chunk::Esi(Tag::Include(attrs)) => {
                            match attrs.iter().find(|&&(name, _)| name == "src") {
                                None => continue,
                                Some(&(_, src)) => {
                                    println!("include src:{}", src);
                                    let reqid = program.requests;
                                    program.requests += 1;

                                    reqids.push_back(reqid);

                                    let mut current = program.last_block();
                                    current.push(Instruction::Request {
                                        reqid: reqid,
                                        url: src.to_owned(),
                                    });
                                }
                            }
                        }
                        _ => continue,
                    }
                }

                if reqids.len() == 0 {
                    // handle the case where the attempt has no includes, i.e. always succeeds
                    // no further attempts or except will be codegen'd as they cannot ever be triggered
                    for chunk in attempt {
                        generate_for_chunk(chunk, program);
                    }
                    attempt_contexts.push_back(None);

                    attempt_no_include = true;
                    break; // bail early
                } else {
                    let attempt_bb = Rc::new(RefCell::new(BasicBlock::new()));
                    let mut current = program.last_block();
                    current.push(Instruction::Success {
                        reqids: reqids.clone().into(),
                    });
                    current.push(Instruction::JumpIf {
                        location: Location::Block(Rc::downgrade(&attempt_bb)),
                    });
                    attempt_contexts.push_back(Some((reqids.clone(), attempt_bb)));
                }
            }

            if let Some(except) = except {
                if !attempt_no_include {
                    for chunk in except {
                        generate_for_chunk(chunk, program);
                    }
                }
            }
            program.last_block().push(Instruction::Jump {
                location: Location::Block(Rc::downgrade(&next_bb)),
            });

            for attempt in attempts {
                let (mut reqids, attempt_bb) = match attempt_contexts.pop_front().unwrap() {
                    Some(c) => c,
                    None => break, // bail early due to an attempt block with no includes
                };

                program.blocks.push(attempt_bb);
                for chunk in attempt {
                    match chunk {
                        Chunk::Esi(Tag::Include(..)) => {
                            let mut current = program.last_block();
                            let reqid = reqids.pop_front().unwrap();
                            current.push(Instruction::WriteResponse { reqid: reqid });
                        }
                        chunk => generate_for_chunk(chunk, program),
                    }
                }
                program.last_block().push(Instruction::Jump {
                    location: Location::Block(Rc::downgrade(&next_bb)),
                });
            }

            program.blocks.push(next_bb);
        }

        tag => println!("unknown esi tag: {:?}", tag),
    }
}

fn generate_for_expr(expr: &Expr, program: &mut Program) {
    match expr {
        Expr::Integer(i) => program.last_block().push(Instruction::Literal {
            value: Value::Integer(*i),
        }),
        Expr::Variable(key, _subkey, _default) => {
            let next_varid = program.variables.len();
            let varid: VarId = *program
                .variables
                .entry(key.to_string())
                .or_insert_with(|| VarId::try_from(next_varid).unwrap());
            program.last_block().push(Instruction::Get { var: varid })
        }
        _ => panic!("unhandled expression type"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::new_parse::parse_document;

    #[test]
    fn test_generate() {
        let input = r#"
<a>foo</a>
<bar />
baz
<esi:vars name="$(hello)">
<esi:vars>
hello <br>
</esi:vars>
<sCripT src="whatever">
<baz>
<script> less < more </script>
<esi:remove>should not appear</esi:remove>
<esi:comment text="also should not appear" />
<esi:text> this <esi:vars>$(should)</esi> appear unchanged</esi:text>
<esi:include src="whatever" />
<esi:choose>
should not appear
</esi:choose>
<esi:choose>
should not appear
<esi:when test="$(whatever)">hi</esi:when>
<esi:otherwise>goodbye</esi:otherwise>
should not appear
</esi:choose>
<esi:try>
should not appear
<esi:attempt>
attempt 1
<esi:include src="/attempt1">
</esi:attempt>
should not appear
<esi:attempt>
attempt 2
<esi:include src="/attempt2">
</esi:attempt>
should not appear
<esi:except>
exception!
</esi:except>
</esi:try>"#;

        let ast = parse_document(input).unwrap();

        let program = generate(ast);
        println!("{:#?}", program);
    }

    #[test]
    fn test_generate_try() {
        let input = r#"
<esi:try>
should not appear
<esi:attempt>
attempt 1
<esi:include src="/attempt1">
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
        println!("{:#?}", program);
    }

    #[test]
    fn test_generate_try_without_include() {
        let input = r#"<esi:try>
<esi:attempt>
<esi:include src="/should-appear">
</esi:attempt>
<esi:attempt>
cannot fail
</esi:attempt>
<esi:attempt>
<esi:include src="/should-not-appear">
</esi:attempt>
<esi:except>
<esi:include src="/should-not-appear-either">
</esi:except>
</esi:try>"#;
        let ast = parse_document(input).unwrap();

        let program = generate(ast);
        println!("{:#?}", program);
    }
}
