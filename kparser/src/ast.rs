use std::iter::once;

use log::{debug, trace};
use pest::error::Error;
use pest::iterators::Pair;
use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "module.pest"]
pub struct KParser;

#[derive(Clone, Debug, PartialEq)]
pub struct Ident(String);

impl From<&str> for Ident {
    fn from(value: &str) -> Self {
        Self(value.to_string())
    }
}

fn parse_string(pair: Pair<'_, Rule>) -> Result<String, Error<Rule>> {
    trace!("Parsing string: {pair:?}");
    assert_eq!(pair.as_rule(), Rule::string_content);

    Ok(pair.as_str().to_string())
}

fn parse_num(pair: Pair<'_, Rule>) -> Result<i128, Error<Rule>> {
    trace!("Parsing number: {pair:?}");
    assert_eq!(pair.as_rule(), Rule::num);

    Ok(pair.as_str().parse().unwrap())
}

fn parse_hex(pair: Pair<'_, Rule>) -> Result<u128, Error<Rule>> {
    trace!("Parsing number: {pair:?}");
    assert_eq!(pair.as_rule(), Rule::hex);

    Ok(u128::from_str_radix(pair.as_str(), 16).unwrap())
}

impl Ident {
    fn from_pair(pair: Pair<'_, Rule>) -> Result<Self, Error<Rule>> {
        trace!("Parsing ident: {pair:?}");
        assert_eq!(pair.as_rule(), Rule::ident);

        Ok(Ident(pair.as_str().to_string()))
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum BinOp {
    EqBool,
    AddInt,
    SubInt,
    MulInt,
    EqInt,
    Add,
    XorBool,
    AndBool,
    OrBool,
}

impl BinOp {
    pub fn level(&self) -> usize {
        match self {
            BinOp::EqBool | BinOp::EqInt => 0,
            BinOp::XorBool | BinOp::OrBool => 1,
            BinOp::AndBool => 2,
            BinOp::Add | BinOp::AddInt | BinOp::SubInt => 5,
            BinOp::MulInt => 10,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum UnOp {
    NotBool,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Var(Ident),
    TraceCons {
        head: Box<Expr>,
        tail: Box<Expr>,
    },
    Compose(Vec<Expr>),
    ExecInstr {
        instr: Box<Expr>,
        operands: Box<Expr>,
    },
    List(Vec<Expr>),
    ListNil(Ident),
    KNil,
    Anything,
    Fun {
        name: Ident,
        args: Vec<Expr>,
    },
    Map {
        from: Box<Expr>,
        to: Box<Expr>,
    },
    String(String),
    Num(i128),
    Hex(u128),
    Dollarydoo,
    Parens(Box<Expr>),
    Ite {
        condition: Box<Expr>,
        then: Box<Expr>,
        otherwise: Box<Expr>,
    },
    BinOp {
        lhs: Box<Expr>,
        op: BinOp,
        rhs: Box<Expr>,
    },
    Typed {
        expr: Box<Expr>,
        ty: Ident,
    },
    Cast {
        expr: Box<Expr>,
        ty: Ident,
    },
    Lookup {
        expr: Box<Expr>,
        key: Box<Expr>,
    },
    UnOp {
        op: UnOp,
        val: Box<Expr>,
    },
}

impl Expr {
    fn from_pair(pair: Pair<'_, Rule>) -> Result<Self, Error<Rule>> {
        trace!("Parsing expr: {pair:?}");
        Ok(match pair.as_rule() {
            Rule::var => Expr::Var(Ident::from_pair(pair.into_inner().next().unwrap())?),
            Rule::trace => {
                let mut pairs = pair.into_inner().rev();
                let mut e = Expr::from_pair(pairs.next().unwrap())?;

                for pair in pairs {
                    e = Expr::TraceCons {
                        head: Box::new(Expr::from_pair(pair)?),
                        tail: Box::new(e),
                    };
                }

                e
            },
            Rule::terms | Rule::terms_without_list => {
                let v = pair.into_inner().map(Expr::from_pair).collect::<Result<Vec<_>, _>>()?;
                if v.len() == 1 {
                    v.into_iter().next().unwrap()
                } else {
                    Expr::Compose(v)
                }
            },
            Rule::execinstr => {
                let mut pairs = pair.into_inner();
                Expr::ExecInstr {
                    instr: Box::new(Expr::from_pair(pairs.next().unwrap())?),
                    operands: Box::new(Expr::from_pair(pairs.next().unwrap())?),
                }
            },
            Rule::nil => Expr::ListNil(Ident::from_pair(pair.into_inner().next().unwrap())?),
            Rule::knil => Expr::KNil,
            Rule::anything => Expr::Anything,
            Rule::fun => {
                let mut pairs = pair.into_inner();
                Expr::Fun {
                    name: Ident::from_pair(pairs.next().unwrap())?,
                    args: pairs.map(Expr::from_pair).collect::<Result<Vec<_>, _>>()?,
                }
            },
            Rule::string_content => Expr::String(parse_string(pair)?),
            Rule::imm => Expr::Compose(pair.into_inner().map(Expr::from_pair).collect::<Result<_, _>>()?),
            Rule::reg => Expr::String(pair.as_str().to_string()),
            Rule::num => Expr::Num(parse_num(pair)?),
            Rule::hex => Expr::Hex(parse_hex(pair)?),
            Rule::special => Expr::String(pair.as_str().to_string()),
            Rule::dollarydoo => Expr::Dollarydoo,
            Rule::ite => {
                let mut pairs = pair.into_inner();
                Expr::Ite {
                    condition: Box::new(Expr::from_pair(pairs.next().unwrap())?),
                    then: Box::new(Expr::from_pair(pairs.next().unwrap())?),
                    otherwise: Box::new(Expr::from_pair(pairs.next().unwrap())?),
                }
            },
            Rule::cast => {
                let mut pairs = pair.into_inner();
                Expr::Cast {
                    expr: Box::new(Expr::from_pair(pairs.next().unwrap())?),
                    ty: Ident::from_pair(pairs.next().unwrap())?,
                }
            },
            Rule::unaryop => {
                let mut pairs = pair.into_inner();
                let op = match pairs.next().unwrap().as_str() {
                    "notBool" => UnOp::NotBool,
                    op => unimplemented!("Unary operator: {op}"),
                };
                Expr::UnOp {
                    op,
                    val: Box::new(Expr::from_pair(pairs.next().unwrap())?),
                }
            },
            Rule::parens => {
                let inner = pair.into_inner().next().unwrap();
                Expr::Parens(Box::new(Expr::from_pair(inner)?))
            },
            Rule::term | Rule::term_without_list => {
                let mut pairs = pair.into_inner();
                let mut result = Expr::from_pair(pairs.next().unwrap())?;

                trace!("Begin term");

                for rhs in pairs {
                    trace!("Term rhs: {rhs:?}");
                    result = match rhs.as_rule() {
                        Rule::binop => {
                            let mut pairs = rhs.into_inner();
                            let op = match pairs.next().unwrap().as_str() {
                                "==Bool" => BinOp::EqBool,
                                "==Int" => BinOp::EqInt,
                                "+" => BinOp::Add,
                                "+Int" => BinOp::AddInt,
                                "-Int" => BinOp::SubInt,
                                "*Int" => BinOp::MulInt,
                                "xorBool" => BinOp::XorBool,
                                "orBool" => BinOp::OrBool,
                                "andBool" => BinOp::AndBool,
                                op => unimplemented!("Binary operator: {op}"),
                            };
                            let rhs = Expr::from_pair(pairs.next().unwrap())?;
                            trace!("lhs={result:?}, rhs={rhs:?}");
                            // Make binary ops left-associative
                            // TODO: Does this work properly?
                            match rhs {
                                Expr::BinOp {
                                    lhs: inner_lhs,
                                    op: inner_op,
                                    rhs: inner_rhs,
                                } if inner_op.level() == op.level() => Expr::BinOp {
                                    lhs: Box::new(Expr::BinOp {
                                        lhs: Box::new(result),
                                        op,
                                        rhs: inner_lhs,
                                    }),
                                    op: inner_op,
                                    rhs: inner_rhs,
                                },
                                rhs => Expr::BinOp {
                                    lhs: Box::new(result),
                                    op,
                                    rhs: Box::new(rhs),
                                },
                            }
                        },
                        Rule::mapping => Expr::Map {
                            from: Box::new(result),
                            to: Box::new(Expr::from_pair(rhs.into_inner().next().unwrap())?),
                        },
                        Rule::typed => Expr::Typed {
                            expr: Box::new(result),
                            ty: Ident::from_pair(rhs.into_inner().next().unwrap())?,
                        },
                        Rule::lookup => Expr::Lookup {
                            expr: Box::new(result),
                            key: Box::new(Expr::from_pair(rhs.into_inner().next().unwrap())?),
                        },
                        Rule::list => Expr::List(
                            once(Ok(result))
                                .chain(rhs.into_inner().map(Expr::from_pair))
                                .collect::<Result<_, _>>()?,
                        ),
                        _ => unimplemented!("{result:?} + {rhs:?}"),
                    };
                }

                result
            },
            _ => unimplemented!("{pair:?}"),
        })
    }

    pub fn parse(source: &str) -> Result<Expr, Error<Rule>> {
        let mut pairs = KParser::parse(Rule::root_expr, source)?;
        debug!("Pairs: {pairs:?}");

        Expr::from_pair(pairs.next().unwrap())
    }

    pub fn untyped(&self) -> &Expr {
        match self {
            Expr::Typed {
                expr, ..
            } => expr,
            other => other,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Rewrite {
    pub from: Expr,
    pub to: Option<Expr>,
}

impl Rewrite {
    fn from_pair(pair: Pair<'_, Rule>) -> Result<Self, Error<Rule>> {
        assert_eq!(pair.as_rule(), Rule::rewrite);
        let mut pair = pair.into_inner();
        Ok(Self {
            from: Expr::from_pair(pair.next().unwrap())?,
            to: if let Some(next) = pair.next() {
                Some(Expr::from_pair(next)?)
            } else {
                None
            },
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Cell {
    pub name: Ident,
    pub rewrite: Rewrite,
    pub allow_before: bool,
    pub allow_after: bool,
}

impl Cell {
    fn from_pair(pair: Pair<'_, Rule>) -> Result<Self, Error<Rule>> {
        assert_eq!(pair.as_rule(), Rule::cell);
        let mut pairs = pair.into_inner().collect::<Vec<_>>();
        let mut allow_before = false;
        let mut allow_after = false;

        let name = Ident::from_pair(pairs.remove(0))?;

        trace!("{name:?} with {pairs:?}");

        if pairs.first().unwrap().as_rule() == Rule::structural_framing {
            allow_before = true;
            pairs.remove(0);
        }

        if pairs.last().unwrap().as_rule() == Rule::structural_framing {
            allow_after = true;
            pairs.pop();
        }

        Ok(Self {
            name,
            rewrite: Rewrite::from_pair(pairs.remove(0))?,
            allow_before,
            allow_after,
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct KRule {
    pub cells: Vec<Cell>,
    pub requires: Vec<Expr>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Statement {
    Imports(Ident),
    Rule(KRule),
    Context,
}

impl Statement {
    fn from_pair(pair: Pair<'_, Rule>) -> Result<Self, Error<Rule>> {
        trace!("Parsing statement: {pair:?}");
        Ok(match pair.as_rule() {
            Rule::imports => Statement::Imports(Ident::from_pair(pair.into_inner().next().unwrap())?),
            Rule::rule => {
                let mut rule = KRule {
                    cells: Vec::new(),
                    requires: Vec::new(),
                };

                for pair in pair.into_inner() {
                    match pair.as_rule() {
                        Rule::rule_requires => rule.requires.push(Expr::from_pair(pair.into_inner().next().unwrap())?),
                        Rule::cell => rule.cells.push(Cell::from_pair(pair)?),
                        _ => unimplemented!("{pair:?}"),
                    }
                }

                Statement::Rule(rule)
            },
            Rule::context => Statement::Context,
            _ => unimplemented!("{pair:?}"),
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Declaration {
    Requires(String),
    Module { name: Ident, body: Vec<Statement> },
}

impl Declaration {
    fn from_pair(pair: Pair<'_, Rule>) -> Result<Self, Error<Rule>> {
        trace!("Parsing declaration: {pair:?}");
        Ok(match pair.as_rule() {
            Rule::requires => Declaration::Requires(parse_string(pair.into_inner().next().unwrap())?),
            Rule::module => {
                let mut inner = pair.into_inner();
                let name = Ident::from_pair(inner.next().unwrap())?;

                Declaration::Module {
                    name,
                    body: inner.map(|pair| Statement::from_pair(pair)).collect::<Result<Vec<_>, _>>()?,
                }
            },
            _ => unimplemented!("{pair:?}"),
        })
    }
}

pub fn parse_rewrite(source: &str) -> Result<Rewrite, Error<Rule>> {
    let mut pairs = KParser::parse(Rule::root_rewrite, source)?;
    debug!("Pairs: {pairs:?}");

    Rewrite::from_pair(pairs.next().unwrap())
}

pub fn parse(source: &str) -> Result<Vec<Declaration>, Error<Rule>> {
    let mut ast = vec![];

    let pairs = KParser::parse(Rule::declarations, source)?;
    debug!("Pairs: {pairs:?}");
    for pair in pairs {
        if pair.as_rule() == Rule::EOI {
            break;
        }

        ast.push(Declaration::from_pair(pair)?);
    }

    Ok(ast)
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use test_log::test;

    use super::*;

    #[test]
    fn parse_empty() {
        match parse(r#""#) {
            Ok(result) => assert_eq!(result, vec![]),
            Err(e) => panic!("{e}"),
        }
    }

    #[test]
    fn parse_comment() {
        match parse(r#"// This is a comment."#) {
            Ok(result) => assert_eq!(result, vec![]),
            Err(e) => panic!("{e}"),
        }
    }

    #[test]
    fn parse_require() {
        match parse(r#"requires "test.k""#) {
            Ok(result) => assert_eq!(result, vec![Declaration::Requires(String::from("test.k"))]),
            Err(e) => panic!("{e}"),
        }
    }

    #[test]
    fn parse_comment_mix() {
        match parse(
            r#"
        // This is a comment.
        requires "test1.k"
        // This is another comment.
        requires "test2.k"
        "#,
        ) {
            Ok(result) => assert_eq!(
                result,
                vec![
                    Declaration::Requires(String::from("test1.k")),
                    Declaration::Requires(String::from("test2.k"))
                ]
            ),
            Err(e) => panic!("{e}"),
        }
    }

    #[test]
    fn parse_module() {
        match parse("module TEST-MODULE endmodule") {
            Ok(result) => assert_eq!(
                result,
                vec![Declaration::Module {
                    name: Ident(String::from("TEST-MODULE")),
                    body: Vec::new(),
                }]
            ),
            Err(e) => panic!("{e}"),
        }
    }

    #[test]
    fn parse_module_body() {
        match parse(
            r#"
        module TEST-MODULE
          imports A
          imports B
        endmodule
        "#,
        ) {
            Ok(result) => assert_eq!(
                result,
                vec![Declaration::Module {
                    name: Ident(String::from("TEST-MODULE")),
                    body: vec![Statement::Imports(Ident::from("A")), Statement::Imports(Ident::from("B")),],
                }]
            ),
            Err(e) => panic!("{e}"),
        }
    }

    #[test]
    fn parse_rule() {
        match parse(
            r#"
        module TEST-MODULE
          rule <k>
            a => b
          </k>
        endmodule
        "#,
        ) {
            Ok(result) => assert_eq!(
                result,
                vec![Declaration::Module {
                    name: Ident(String::from("TEST-MODULE")),
                    body: vec![Statement::Rule(KRule {
                        cells: vec![Cell {
                            name: Ident::from("k"),
                            rewrite: Rewrite {
                                from: Expr::Var(Ident::from("a")),
                                to: Some(Expr::Var(Ident::from("b"))),
                            },
                            allow_before: false,
                            allow_after: false,
                        }],
                        requires: Vec::new(),
                    }),],
                }]
            ),
            Err(e) => panic!("{e}"),
        }
    }

    #[test]
    fn parse_associativity() {
        match parse_rewrite(r#"1 => A +Int B -Int C"#) {
            Ok(result) => assert_eq!(
                result,
                Rewrite {
                    from: Expr::Num(1),
                    to: Some(Expr::BinOp {
                        lhs: Box::new(Expr::BinOp {
                            lhs: Box::new(Expr::Var(Ident::from("A"))),
                            op: BinOp::AddInt,
                            rhs: Box::new(Expr::Var(Ident::from("B"))),
                        }),
                        op: BinOp::SubInt,
                        rhs: Box::new(Expr::Var(Ident::from("C"))),
                    }),
                }
            ),
            Err(e) => panic!("{e}"),
        }

        match parse_rewrite(r#"1 => A +Int (B -Int C)"#) {
            Ok(result) => assert_eq!(
                result,
                Rewrite {
                    from: Expr::Num(1),
                    to: Some(Expr::BinOp {
                        lhs: Box::new(Expr::Var(Ident::from("A"))),
                        op: BinOp::AddInt,
                        rhs: Box::new(Expr::Parens(Box::new(Expr::BinOp {
                            lhs: Box::new(Expr::Var(Ident::from("B"))),
                            op: BinOp::SubInt,
                            rhs: Box::new(Expr::Var(Ident::from("C"))),
                        }))),
                    }),
                }
            ),
            Err(e) => panic!("{e}"),
        }

        match parse_rewrite(r#"1 => A +Int B *Int C"#) {
            Ok(result) => assert_eq!(
                result,
                Rewrite {
                    from: Expr::Num(1),
                    to: Some(Expr::BinOp {
                        lhs: Box::new(Expr::Var(Ident::from("A"))),
                        op: BinOp::AddInt,
                        rhs: Box::new(Expr::BinOp {
                            lhs: Box::new(Expr::Var(Ident::from("B"))),
                            op: BinOp::MulInt,
                            rhs: Box::new(Expr::Var(Ident::from("C"))),
                        }),
                    }),
                }
            ),
            Err(e) => panic!("{e}"),
        }
    }

    #[test]
    fn parse_num() {
        match parse_rewrite(
            r#"1 => updateMap(RSMap,
            A |-> B
            C |-> D
            )"#,
        ) {
            Ok(result) => assert_eq!(
                result,
                Rewrite {
                    from: Expr::Num(1),
                    to: Some(Expr::Fun {
                        name: Ident::from("updateMap"),
                        args: vec![
                            Expr::Var(Ident::from("RSMap")),
                            Expr::Compose(vec![
                                Expr::Map {
                                    from: Box::new(Expr::Var(Ident::from("A"))),
                                    to: Box::new(Expr::Var(Ident::from("B")))
                                },
                                Expr::Map {
                                    from: Box::new(Expr::Var(Ident::from("C"))),
                                    to: Box::new(Expr::Var(Ident::from("D")))
                                }
                            ])
                        ]
                    }),
                }
            ),
            Err(e) => panic!("{e}"),
        }
    }

    #[test]
    fn test_expr_shouldnt_consume_keyword() {
        match parse(
            r#"
            module TEST
                rule
                    requires a b
            endmodule
            "#,
        ) {
            Ok(result) => assert_eq!(
                result,
                vec![Declaration::Module {
                    name: Ident(String::from("TEST")),
                    body: vec![Statement::Rule(KRule {
                        cells: Vec::new(),
                        requires: vec![Expr::Compose(vec![Expr::Var(Ident::from("a")), Expr::Var(Ident::from("b")),])],
                    }),],
                }]
            ),
            Err(e) => panic!("{e}"),
        }
    }

    #[test]
    fn context_should_parse() {
        match parse(
            r#"
            module TEST
                context execinstr(call:Opcode (HOLE:Mem, .Operands):Operands) [result(MemOffset)]
            endmodule
            "#,
        ) {
            Ok(result) => assert_eq!(
                result,
                vec![Declaration::Module {
                    name: Ident(String::from("TEST")),
                    body: vec![Statement::Context,],
                }]
            ),
            Err(e) => panic!("{e}"),
        }
    }

    #[test]
    fn parse_cmovll_r32_r32() {
        match parse(
            r#"// Autogenerated using stratification.
        requires "x86-configuration.k"
        
        module CMOVLL-R32-R32
          imports X86-CONFIGURATION
        
          rule <k>
            execinstr (cmovll R1:R32, R2:R32,  .Operands) => .
          ...</k>
            <regstate>
        RSMap:Map => updateMap(RSMap,
        convToRegKeys(R2) |-> concatenateMInt( mi(32, 0), (#ifMInt (notBool (eqMInt(getFlag("SF", RSMap), mi(1,1)) ==Bool eqMInt(getFlag("OF", RSMap), mi(1,1)))) #then extractMInt( getParentValue(R1, RSMap), 32, 64) #else extractMInt( getParentValue(R2, RSMap), 32, 64) #fi))
        )
        
            </regstate>
            
        endmodule
        
        module CMOVLL-R32-R32-SEMANTICS
          imports CMOVLL-R32-R32
        endmodule
        "#,
        ) {
            Ok(result) => {
                let r2update = Box::new(Expr::Fun {
                    name: Ident::from("concatenateMInt"),
                    args: vec![
                        Expr::Fun {
                            name: Ident::from("mi"),
                            args: vec![Expr::Num(32), Expr::Num(0)],
                        },
                        Expr::Ite {
                            condition: Box::new(Expr::Fun {
                                name: Ident::from("notBool"),
                                args: vec![Expr::BinOp {
                                    lhs: Box::new(Expr::Fun {
                                        name: Ident::from("eqMInt"),
                                        args: vec![
                                            Expr::Fun {
                                                name: Ident::from("getFlag"),
                                                args: vec![Expr::String(String::from("SF")), Expr::Var(Ident::from("RSMap"))],
                                            },
                                            Expr::Fun {
                                                name: Ident::from("mi"),
                                                args: vec![Expr::Num(1), Expr::Num(1)],
                                            },
                                        ],
                                    }),
                                    op: BinOp::EqBool,
                                    rhs: Box::new(Expr::Fun {
                                        name: Ident::from("eqMInt"),
                                        args: vec![
                                            Expr::Fun {
                                                name: Ident::from("getFlag"),
                                                args: vec![Expr::String(String::from("OF")), Expr::Var(Ident::from("RSMap"))],
                                            },
                                            Expr::Fun {
                                                name: Ident::from("mi"),
                                                args: vec![Expr::Num(1), Expr::Num(1)],
                                            },
                                        ],
                                    }),
                                }],
                            }),
                            then: Box::new(Expr::Fun {
                                name: Ident::from("extractMInt"),
                                args: vec![
                                    Expr::Fun {
                                        name: Ident::from("getParentValue"),
                                        args: vec![Expr::Var(Ident::from("R1")), Expr::Var(Ident::from("RSMap"))],
                                    },
                                    Expr::Num(32),
                                    Expr::Num(64),
                                ],
                            }),
                            otherwise: Box::new(Expr::Fun {
                                name: Ident::from("extractMInt"),
                                args: vec![
                                    Expr::Fun {
                                        name: Ident::from("getParentValue"),
                                        args: vec![Expr::Var(Ident::from("R2")), Expr::Var(Ident::from("RSMap"))],
                                    },
                                    Expr::Num(32),
                                    Expr::Num(64),
                                ],
                            }),
                        },
                    ],
                });

                assert_eq!(
                    result,
                    vec![
                        Declaration::Requires(String::from("x86-configuration.k")),
                        Declaration::Module {
                            name: Ident::from("CMOVLL-R32-R32"),
                            body: vec![
                                Statement::Imports(Ident::from("X86-CONFIGURATION")),
                                Statement::Rule(KRule {
                                    cells: vec![
                                        Cell {
                                            name: Ident::from("k"),
                                            rewrite: Rewrite {
                                                from: Expr::ExecInstr {
                                                    instr: Box::new(Expr::Var(Ident::from("cmovll"))),
                                                    operands: Box::new(Expr::List(vec![
                                                        Expr::Typed {
                                                            expr: Box::new(Expr::Var(Ident::from("R1"))),
                                                            ty: Ident::from("R32"),
                                                        },
                                                        Expr::Typed {
                                                            expr: Box::new(Expr::Var(Ident::from("R2"))),
                                                            ty: Ident::from("R32"),
                                                        },
                                                        Expr::ListNil(Ident::from("Operands"))
                                                    ]))
                                                },
                                                to: Some(Expr::KNil)
                                            },
                                            allow_before: false,
                                            allow_after: true,
                                        },
                                        Cell {
                                            name: Ident::from("regstate"),
                                            rewrite: Rewrite {
                                                from: Expr::Typed {
                                                    expr: Box::new(Expr::Var(Ident::from("RSMap"))),
                                                    ty: Ident::from("Map"),
                                                },
                                                to: Some(Expr::Fun {
                                                    name: Ident::from("updateMap"),
                                                    args: vec![
                                                        Expr::Var(Ident::from("RSMap")),
                                                        Expr::Map {
                                                            from: Box::new(Expr::Fun {
                                                                name: Ident::from("convToRegKeys"),
                                                                args: vec![Expr::Var(Ident::from("R2"))]
                                                            }),
                                                            to: r2update,
                                                        }
                                                    ]
                                                })
                                            },
                                            allow_before: false,
                                            allow_after: false,
                                        }
                                    ],
                                    requires: Vec::new(),
                                })
                            ]
                        },
                        Declaration::Module {
                            name: Ident::from("CMOVLL-R32-R32-SEMANTICS"),
                            body: vec![Statement::Imports(Ident::from("CMOVLL-R32-R32"))]
                        }
                    ]
                )
            },
            Err(e) => panic!("{e}"),
        }
    }

    #[test]
    #[ignore]
    pub fn parse_all_definitions() {
        let base = PathBuf::from("../../../X86-64-semantics/semantics/");
        println!("Current directory {:?}", std::env::current_dir());
        let files = [
            "immediateInstructions",
            "memoryInstructions",
            "registerInstructions",
            "systemInstructions",
        ]
        .map(|dir| base.join(dir))
        .iter()
        .flat_map(|dir| {
            println!("Reading {dir:?}");
            std::fs::read_dir(dir).expect("Directory not found")
        })
        .map(|item| item.unwrap().path())
        .collect::<Vec<_>>();

        println!("Files to check: {}", files.len());

        let mut fails = Vec::new();
        let mut num_simple = 0usize;

        for (index, file) in files.iter().enumerate() {
            println!("Checking {index} / {}: {file:?}", files.len());
            let content = std::fs::read_to_string(file).unwrap();
            match parse(&content) {
                Ok(declarations) => {
                    let d = declarations.iter()
                        .filter(|decl| matches!(decl, Declaration::Module { body, .. } if body.iter().any(|stmt| matches!(stmt, Statement::Rule(_)))))
                        .collect::<Vec<_>>();
                    if d.len() == 1
                        && match d[0] {
                            Declaration::Module {
                                body, ..
                            } => {
                                let s = body
                                    .iter()
                                    .filter(|stmt| matches!(stmt, Statement::Rule(_)))
                                    .collect::<Vec<_>>();
                                if s.len() == 1 {
                                    match s[0] {
                                        Statement::Rule(rule) => rule.requires.is_empty(),
                                        _ => unreachable!(),
                                    }
                                } else {
                                    false
                                }
                            },
                            _ => unreachable!(),
                        }
                    {
                        println!("Simple");
                        num_simple += 1;
                    } else {
                        println!("Not simple");
                    }
                },
                Err(e) => {
                    fails.push(file);
                    println!("{e}")
                },
            }
        }

        println!("{fails:#?}");
        println!("Num simple: {num_simple}");
        assert!(fails.is_empty(), "{} / {} failed", fails.len(), files.len());
    }
}
