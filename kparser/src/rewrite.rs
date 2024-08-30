use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

use itertools::{EitherOrBoth, Itertools};
use log::{debug, info, trace};

use crate::ast::{BinOp, Declaration, Expr, KRule, Statement, UnOp};
use crate::util::{Id, IdMap, IndexMap};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct CellId(usize);

impl Id for CellId {
    fn from_usize(val: usize) -> Self {
        Self(val)
    }

    fn as_index(&self) -> usize {
        self.0
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VarId(usize);

impl Id for VarId {
    fn from_usize(val: usize) -> Self {
        Self(val)
    }

    fn as_index(&self) -> usize {
        self.0
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ListKind {
    Trace,
    Compose,
    Comma,
    Map,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Ty(Vec<TokenTree>);

#[derive(Clone, PartialEq)]
pub enum TokenTree {
    List {
        kind: ListKind,
        head: Box<TokenTree>,
        tail: Box<TokenTree>,
    },
    Fun {
        name: String,
        args: Vec<TokenTree>,
    },
    MapTo {
        from: Box<TokenTree>,
        to: Box<TokenTree>,
    },
    Typed {
        expr: Box<TokenTree>,
        ty: Ty,
    },
    Var(VarId),
    String(String),
    Num(i128),
    Hex(u128),
    Dollarydoo,
    Nil,
    Anything,
}

impl Debug for TokenTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenTree::List {
                kind,
                head,
                tail,
            } => write!(f, "{kind:?}({head:?}, {tail:?})"),
            TokenTree::Var(arg0) => write!(f, "var{}", arg0.as_index()),
            TokenTree::Fun {
                name,
                args,
            } => write!(f, "{}({:?})", name, args.iter().format(", ")),
            TokenTree::MapTo {
                from,
                to,
            } => write!(f, "{from:?} |-> {to:?}"),
            TokenTree::Nil => write!(f, "()"),
            TokenTree::Anything => write!(f, "..."),
            TokenTree::String(s) => write!(f, "{s:?}"),
            TokenTree::Num(n) => write!(f, "{n}"),
            TokenTree::Hex(n) => write!(f, "0x{n:X}"),
            TokenTree::Dollarydoo => write!(f, "$"),
            TokenTree::Typed {
                expr,
                ty,
            } => write!(f, "({expr:?}):{ty:?}"),
        }
    }
}

impl TokenTree {
    // Self is the cell state, other is the rule
    fn matches<'a>(&'a self, other: &'a TokenTree, mapping: &mut IndexMap<VarId, &'a TokenTree>) -> bool {
        let matches = match (self, other) {
            // TODO: What are the semantics of "..." supposed to be?
            (TokenTree::Anything, TokenTree::Anything) | (_, TokenTree::Anything) => true,
            (
                me,
                TokenTree::Typed {
                    expr,
                    ty,
                },
            ) => ty.0.iter().any(|t| me.matches(t, mapping)) && me.matches(expr, mapping),
            (
                TokenTree::Typed {
                    expr, ..
                },
                other,
            ) => expr.matches(other, mapping),
            (TokenTree::Var(a), TokenTree::Var(b)) => match (mapping[a], mapping[b]) {
                (Some(tt_a), Some(tt_b)) => tt_a.matches(tt_b, mapping),
                (Some(tt), None) => {
                    mapping[b] = Some(tt);
                    true
                },
                (None, Some(tt)) => {
                    mapping[a] = Some(tt);
                    true
                },
                (None, None) => {
                    mapping[a] = Some(other);
                    mapping[b] = Some(self);
                    true
                },
            },
            (tt, TokenTree::Var(var_id)) => {
                if let Some(m) = mapping[var_id] {
                    tt.matches(m, mapping)
                } else {
                    mapping[var_id] = Some(tt);
                    true
                }
            },
            (
                TokenTree::List {
                    kind: kind_a,
                    head: head_a,
                    tail: tail_a,
                },
                TokenTree::List {
                    kind: kind_b,
                    head: head_b,
                    tail: tail_b,
                },
            ) => kind_a == kind_b && head_a.matches(head_b, mapping) && tail_a.matches(tail_b, mapping),
            (
                TokenTree::Fun {
                    name: name_a,
                    args: args_a,
                },
                TokenTree::Fun {
                    name: name_b,
                    args: args_b,
                },
            ) => {
                name_a == name_b
                    && args_a.len() == args_b.len()
                    && args_a.iter().zip(args_b.iter()).all(|(a, b)| a.matches(b, mapping))
            },
            (
                TokenTree::MapTo {
                    from: from_a,
                    to: to_a,
                },
                TokenTree::MapTo {
                    from: from_b,
                    to: to_b,
                },
            ) => from_a.matches(from_b, mapping) && to_a.matches(to_b, mapping),
            (TokenTree::String(a), TokenTree::String(b)) => a == b,
            (TokenTree::Num(a), TokenTree::Num(b)) => a == b,
            (TokenTree::Hex(a), TokenTree::Hex(b)) => a == b,
            (TokenTree::Dollarydoo, TokenTree::Dollarydoo) => true,
            (TokenTree::Nil, TokenTree::Nil) => true,
            _ => false,
        };

        if !matches {
            trace!("inner matches(): {self:?} vs {other:?} = false");
        }

        matches
    }

    fn as_cons(&self) -> (&TokenTree, &TokenTree) {
        if let TokenTree::List {
            head,
            tail,
            ..
        } = self
        {
            (&**head, &**tail)
        } else {
            (self, &TokenTree::Nil)
        }
    }

    fn reduce(&mut self) -> bool {
        let mut any = false;
        loop {
            let repeat = match self {
                TokenTree::List {
                    kind: ListKind::Trace,
                    head,
                    tail,
                    ..
                } if matches!(&**tail, &TokenTree::Nil) => {
                    *self = (**head).clone();
                    true
                },
                TokenTree::List {
                    head,
                    tail,
                    ..
                } if matches!(&**head, &TokenTree::Nil) => {
                    *self = (**tail).clone();
                    true
                },
                TokenTree::List {
                    kind,
                    head,
                    tail,
                } => {
                    let mut repeat = head.reduce() | tail.reduce();
                    if let TokenTree::List {
                        kind: inner_kind,
                        head: inner_head,
                        tail: inner_tail,
                    } = &**head
                    {
                        if kind == inner_kind {
                            *self = TokenTree::List {
                                kind: *kind,
                                head: inner_head.clone(),
                                tail: Box::new(TokenTree::List {
                                    kind: *kind,
                                    head: inner_tail.clone(),
                                    tail: tail.clone(),
                                }),
                            };
                            repeat = true;
                        }
                    }

                    repeat
                },
                TokenTree::Fun {
                    name,
                    args,
                } => {
                    let repeat = args.iter_mut().any(|arg| arg.reduce());

                    let repeat = repeat
                        | match (name.as_str(), args.as_slice()) {
                            ("__sub_int", &[TokenTree::Num(a), TokenTree::Num(b)]) => {
                                *self = TokenTree::Num(a - b);
                                true
                            },
                            ("__add_int", &[TokenTree::Num(a), TokenTree::Num(b)]) => {
                                *self = TokenTree::Num(a + b);
                                true
                            },
                            // __lookup(key |-> value, ...)
                            ("__lookup", [map, key]) => {
                                let (head, tail) = map.as_cons();
                                if let TokenTree::MapTo {
                                    from,
                                    to,
                                } = head
                                {
                                    let can_apply = match key {
                                        TokenTree::String(_) => true,
                                        TokenTree::Fun {
                                            name, ..
                                        } => name == "z3_mem",
                                        _ => false,
                                    };

                                    if can_apply {
                                        if &**from == key {
                                            *self = (**to).clone();
                                        } else {
                                            *self = TokenTree::Fun {
                                                name: String::from("__lookup"),
                                                args: vec![tail.clone(), key.clone()],
                                            };
                                        }

                                        true
                                    } else {
                                        false
                                    }
                                } else {
                                    false
                                }
                            },
                            // removeKey base case
                            ("removeKey", [TokenTree::Nil, _]) => {
                                *self = TokenTree::Nil;

                                true
                            },
                            // removeKey recursive case
                            ("removeKey", [map, key]) => {
                                let (map_head, map_tail) = map.as_cons();

                                if let TokenTree::MapTo {
                                    from, ..
                                } = map_head
                                {
                                    let can_apply = match &**from {
                                        TokenTree::String(_) => true,
                                        TokenTree::Fun {
                                            name, ..
                                        } => name == "z3_mem",
                                        _ => false,
                                    };
                                    if can_apply {
                                        if &**from == key {
                                            *self = map_tail.clone();
                                        } else {
                                            *self = TokenTree::List {
                                                kind: ListKind::Comma,
                                                head: Box::new(map_head.clone()),
                                                tail: Box::new(TokenTree::Fun {
                                                    name: String::from("removeKey"),
                                                    args: vec![map_tail.clone(), key.clone()],
                                                }),
                                            };
                                        }

                                        any = true;

                                        true
                                    } else {
                                        false
                                    }
                                } else {
                                    false
                                }
                            },
                            // updateMap(map, key |-> value rest) => updateMap(updateMap(map, key |-> value), rest)
                            (
                                "updateMap",
                                [
                                    map,
                                    TokenTree::List {
                                        head,
                                        tail,
                                        ..
                                    },
                                ],
                            ) => {
                                *self = TokenTree::Fun {
                                    name: String::from("updateMap"),
                                    args: vec![
                                        TokenTree::Fun {
                                            name: String::from("updateMap"),
                                            args: vec![map.clone(), (**head).clone()],
                                        },
                                        (**tail).clone(),
                                    ],
                                };

                                true
                            },
                            // // updateMap(map, key |-> value rest) => updateMap(updateMap(map, key |-> value), rest)
                            // ("updateMap", [ TokenTree::Nil, _ ]) => {
                            //     *self = TokenTree::Nil;

                            //     true
                            // }
                            // updateMap(map, nil) => map
                            ("updateMap", [v, TokenTree::Nil]) => {
                                *self = v.clone();

                                true
                            },
                            // // updateMap((lhskey |-> lhsvalue, ...), rhskey |-> rhsvalue) = lhskey |-> value/newvalue, updateMap(..., rhskey |-> rhsvalue)
                            // ("updateMap", [ map, update @ TokenTree::MapTo { from, .. } ]) => {
                            //     let (map_head, map_tail) = map.as_cons();

                            //     if let TokenTree::MapTo { from: map_from, .. } = map_head {
                            //         if let (TokenTree::String(map_key), TokenTree::String(update_key)) = (&**map_from, &**from) {
                            //             let new = TokenTree::List {
                            //                 kind: ListKind::Comma,
                            //                 head: Box::new(if map_key == update_key {
                            //                     update.clone()
                            //                 } else {
                            //                     map_head.clone()
                            //                 }),
                            //                 tail: Box::new(TokenTree::Fun {
                            //                     name: String::from("updateMap"),
                            //                     args: vec![
                            //                         map_tail.clone(),
                            //                         update.clone(),
                            //                     ],
                            //                 }),
                            //             };
                            //             debug!("Reducing: {self:?} => {new:?}");
                            //             *self = new;

                            //             any = true;

                            //             true
                            //         } else {
                            //             false
                            //         }
                            //     } else {
                            //         false
                            //     }
                            // },
                            ("convSubRegsToRegs", [TokenTree::String(reg)]) => {
                                *self = TokenTree::String(String::from(match reg.as_str() {
                                    "%virt:R8:0" => "%virt:R64:0",
                                    "%virt:R8:1" => "%virt:R64:1",
                                    "%virt:R8:2" => "%virt:R64:2",
                                    "%virt:Rh:0" => "%virt:R64:0",
                                    "%virt:Rh:1" => "%virt:R64:1",
                                    "%virt:Rh:2" => "%virt:R64:2",
                                    "%virt:R16:0" => "%virt:R64:0",
                                    "%virt:R16:1" => "%virt:R64:1",
                                    "%virt:R16:2" => "%virt:R64:2",
                                    "%virt:R32:0" => "%virt:R64:0",
                                    "%virt:R32:1" => "%virt:R64:1",
                                    "%virt:R32:2" => "%virt:R64:2",
                                    "%virt:R64:0" => "%virt:R64:0",
                                    "%virt:R64:1" => "%virt:R64:1",
                                    "%virt:R64:2" => "%virt:R64:2",
                                    "%virt:Xmm:0" => "%virt:Ymm:0",
                                    "%virt:Xmm:1" => "%virt:Ymm:1",
                                    "%virt:Xmm:2" => "%virt:Ymm:2",
                                    "%virt:Xmm:3" => "%virt:Ymm:3",
                                    "%virt:Ymm:0" => "%virt:Ymm:0",
                                    "%virt:Ymm:1" => "%virt:Ymm:1",
                                    "%virt:Ymm:2" => "%virt:Ymm:2",
                                    "%virt:Ymm:3" => "%virt:Ymm:3",

                                    "%al" => "%rax",
                                    "%ah" => "%rax",
                                    "%ax" => "%rax",
                                    "%eax" => "%rax",
                                    "%rax" => "%rax",

                                    "%bl" => "%rbx",
                                    "%bh" => "%rbx",
                                    "%bx" => "%rbx",
                                    "%ebx" => "%rbx",
                                    "%rbx" => "%rbx",

                                    "%cl" => "%rcx",
                                    "%ch" => "%rcx",
                                    "%cx" => "%rcx",
                                    "%ecx" => "%rcx",
                                    "%rcx" => "%rcx",

                                    "%dl" => "%rdx",
                                    "%dh" => "%rdx",
                                    "%dx" => "%rdx",
                                    "%edx" => "%rdx",
                                    "%rdx" => "%rdx",

                                    "%sil" => "%rsi",
                                    "%si" => "%rsi",
                                    "%esi" => "%rsi",
                                    "%rsi" => "%rsi",

                                    "%dil" => "%rdi",
                                    "%di" => "%rdi",
                                    "%edi" => "%rdi",
                                    "%rdi" => "%rdi",

                                    "%spl" => "%rsp",
                                    "%sp" => "%rsp",
                                    "%esp" => "%rsp",
                                    "%rsp" => "%rsp",

                                    "%bpl" => "%rbp",
                                    "%bp" => "%rbp",
                                    "%ebp" => "%rbp",
                                    "%rbp" => "%rbp",

                                    "%r8b" => "%r8",
                                    "%r8w" => "%r8",
                                    "%r8d" => "%r8",
                                    "%r8" => "%r8",

                                    "%r9b" => "%r9",
                                    "%r9w" => "%r9",
                                    "%r9d" => "%r9",
                                    "%r9" => "%r9",

                                    "%r10b" => "%r10",
                                    "%r10w" => "%r10",
                                    "%r10d" => "%r10",
                                    "%r10" => "%r10",

                                    "%r11b" => "%r11",
                                    "%r11w" => "%r11",
                                    "%r11d" => "%r11",
                                    "%r11" => "%r11",

                                    "%r12b" => "%r12",
                                    "%r12w" => "%r12",
                                    "%r12d" => "%r12",
                                    "%r12" => "%r12",

                                    "%r13b" => "%r13",
                                    "%r13w" => "%r13",
                                    "%r13d" => "%r13",
                                    "%r13" => "%r13",

                                    "%r14b" => "%r14",
                                    "%r14w" => "%r14",
                                    "%r14d" => "%r14",
                                    "%r14" => "%r14",

                                    "%r15b" => "%r15",
                                    "%r15w" => "%r15",
                                    "%r15d" => "%r15",
                                    "%r15" => "%r15",

                                    "%xmm0" => "%ymm0",
                                    "%xmm1" => "%ymm1",
                                    "%xmm2" => "%ymm2",
                                    "%xmm3" => "%ymm3",
                                    "%xmm4" => "%ymm4",
                                    "%xmm5" => "%ymm5",
                                    "%xmm6" => "%ymm6",
                                    "%xmm7" => "%ymm7",
                                    "%xmm8" => "%ymm8",
                                    "%xmm9" => "%ymm9",
                                    "%xmm10" => "%ymm10",
                                    "%xmm11" => "%ymm11",
                                    "%xmm12" => "%ymm12",
                                    "%xmm13" => "%ymm13",
                                    "%xmm14" => "%ymm14",
                                    "%xmm15" => "%ymm15",

                                    "%ymm0" => "%ymm0",
                                    "%ymm1" => "%ymm1",
                                    "%ymm2" => "%ymm2",
                                    "%ymm3" => "%ymm3",
                                    "%ymm4" => "%ymm4",
                                    "%ymm5" => "%ymm5",
                                    "%ymm6" => "%ymm6",
                                    "%ymm7" => "%ymm7",
                                    "%ymm8" => "%ymm8",
                                    "%ymm9" => "%ymm9",
                                    "%ymm10" => "%ymm10",
                                    "%ymm11" => "%ymm11",
                                    "%ymm12" => "%ymm12",
                                    "%ymm13" => "%ymm13",
                                    "%ymm14" => "%ymm14",
                                    "%ymm15" => "%ymm15",

                                    other => panic!("convSubRegsToRegs({other}): register unknown"),
                                }));

                                false
                            },
                            ("convToRegKeysHelper", [TokenTree::String(reg)]) => {
                                *self = TokenTree::String(String::from(match reg.as_str() {
                                    "%virt:R64:0" => "%virt:R64:0",
                                    "%virt:R64:1" => "%virt:R64:1",
                                    "%virt:R64:2" => "%virt:R64:2",
                                    "%virt:Ymm:0" => "%virt:Ymm:0",
                                    "%virt:Ymm:1" => "%virt:Ymm:1",
                                    "%virt:Ymm:2" => "%virt:Ymm:2",
                                    "%virt:Ymm:3" => "%virt:Ymm:3",

                                    "%rax" => "RAX",
                                    "%rbx" => "RBX",
                                    "%rcx" => "RCX",
                                    "%rdx" => "RDX",
                                    "%rsi" => "RSI",
                                    "%rdi" => "RDI",
                                    "%rsp" => "RSP",
                                    "%rbp" => "RBP",
                                    "%r8" => "R8",
                                    "%r9" => "R9",
                                    "%r10" => "R10",
                                    "%r11" => "R11",
                                    "%r12" => "R12",
                                    "%r13" => "R13",
                                    "%r14" => "R14",
                                    "%r15" => "R15",
                                    "%ymm0" => "YMM0",
                                    "%ymm1" => "YMM1",
                                    "%ymm2" => "YMM2",
                                    "%ymm3" => "YMM3",
                                    "%ymm4" => "YMM4",
                                    "%ymm5" => "YMM5",
                                    "%ymm6" => "YMM6",
                                    "%ymm7" => "YMM7",
                                    "%ymm8" => "YMM8",
                                    "%ymm9" => "YMM9",
                                    "%ymm10" => "YMM10",
                                    "%ymm11" => "YMM11",
                                    "%ymm12" => "YMM12",
                                    "%ymm13" => "YMM13",
                                    "%ymm14" => "YMM14",
                                    "%ymm15" => "YMM15",

                                    other => panic!("convToRegKeysHelper({other}): register unknown"),
                                }));

                                false
                            },
                            _ => false,
                        };

                    repeat
                },
                TokenTree::MapTo {
                    from,
                    to,
                } => from.reduce() | to.reduce(),
                TokenTree::Typed {
                    expr, ..
                } => expr.reduce(),
                TokenTree::Anything
                | TokenTree::Nil
                | TokenTree::Var(_)
                | TokenTree::String(_)
                | TokenTree::Num(_)
                | TokenTree::Hex(_)
                | TokenTree::Dollarydoo => false,
            };

            any |= repeat;

            if !repeat {
                break any
            }
        }
    }

    fn substitute(&mut self, mapping: &IndexMap<VarId, TokenTree>) {
        match self {
            TokenTree::Var(var_id) => {
                let var_id = *var_id;
                if let Some(new) = mapping[var_id].as_ref() {
                    *self = new.clone();
                } else {
                    panic!("Variable {self:?} is not bound in mapping: {mapping:?}");
                }
            },
            TokenTree::List {
                head,
                tail,
                ..
            } => {
                head.substitute(mapping);
                tail.substitute(mapping);
            },
            TokenTree::Fun {
                args, ..
            } => {
                for arg in args.iter_mut() {
                    arg.substitute(mapping);
                }
            },
            TokenTree::MapTo {
                from,
                to,
            } => {
                from.substitute(mapping);
                to.substitute(mapping);
            },
            TokenTree::Nil => (),
            TokenTree::Anything => (),
            TokenTree::Typed {
                expr, ..
            } => expr.substitute(mapping),
            TokenTree::String(_) | TokenTree::Num(_) | TokenTree::Hex(_) | TokenTree::Dollarydoo => (),
        }
    }

    fn collect_varids(&self, output: &mut Vec<VarId>) {
        match self {
            TokenTree::List {
                head,
                tail,
                ..
            } => {
                head.collect_varids(output);
                tail.collect_varids(output);
            },
            TokenTree::Fun {
                args, ..
            } => {
                for arg in args {
                    arg.collect_varids(output);
                }
            },
            TokenTree::MapTo {
                from,
                to,
            } => {
                from.collect_varids(output);
                to.collect_varids(output);
            },
            TokenTree::Typed {
                expr, ..
            } => expr.collect_varids(output),
            TokenTree::Var(v) => output.push(*v),
            TokenTree::String(_)
            | TokenTree::Num(_)
            | TokenTree::Hex(_)
            | TokenTree::Dollarydoo
            | TokenTree::Nil
            | TokenTree::Anything => (),
        }
    }

    fn find_match(
        &mut self, other: &TokenTree, base_mapping: &IndexMap<VarId, TokenTree>, framing: &Framing,
    ) -> Option<(&mut TokenTree, IndexMap<VarId, TokenTree>)> {
        let mut mapping = base_mapping.as_ref();
        let is_match = self.matches(other, &mut mapping);
        trace!("matches({self:?}, {other:?}) with mapping {mapping:?} and = {is_match}");
        if is_match {
            let mapping = mapping.map(|val| val.clone());
            Some((self, mapping))
        } else {
            match self {
                TokenTree::List {
                    head,
                    tail,
                    ..
                } => {
                    if framing.allow_after {
                        if let Some(x) = head.find_match(other, base_mapping, framing) {
                            return Some(x)
                        }
                    }

                    if framing.allow_before {
                        if let Some(x) = tail.find_match(other, base_mapping, framing) {
                            return Some(x)
                        }
                    }

                    None
                },
                TokenTree::Fun {
                    args, ..
                } => {
                    if framing.allow_after && framing.allow_before {
                        for item in args.iter_mut() {
                            if let Some(x) = item.find_match(other, base_mapping, framing) {
                                return Some(x)
                            }
                        }
                    }

                    None
                },
                TokenTree::MapTo {
                    from,
                    to,
                } => {
                    if let Some(x) = from.find_match(other, base_mapping, framing) {
                        Some(x)
                    } else {
                        to.find_match(other, base_mapping, framing)
                    }
                },
                TokenTree::Typed {
                    expr, ..
                } => expr.find_match(other, base_mapping, framing),
                TokenTree::Var(_)
                | TokenTree::String(_)
                | TokenTree::Num(_)
                | TokenTree::Hex(_)
                | TokenTree::Dollarydoo
                | TokenTree::Nil
                | TokenTree::Anything => None,
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct CellState {
    pub tokens: TokenTree,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Framing {
    allow_before: bool,
    allow_after: bool,
}

#[derive(Debug)]
pub struct TokenRewrite {
    from: TokenTree,
    to: Option<TokenTree>,
    framing: Framing,
}

#[derive(Debug)]
pub struct TokenRule {
    rewrites: IndexMap<CellId, TokenRewrite>,
    requires: Vec<TokenTree>,
}

#[derive(Debug)]
pub struct PendingRewrite<'a> {
    tt: &'a mut TokenTree,
    to: &'a TokenTree,
}

#[derive(Default)]
pub struct ExecutionEnv {
    rules: Vec<TokenRule>,
    conditional_rules: Vec<TokenRule>,
    cell_ids: IdMap<CellId>,
    var_ids: IdMap<VarId>,
    initial_state: ExecutionState,
    types: HashMap<String, Vec<TokenTree>>,
}

#[derive(Clone, Debug, Default)]
pub struct ExecutionState {
    path_constraints: Vec<TokenTree>,
    cells: IndexMap<CellId, CellState>,
}

impl ExecutionState {
    pub fn path_constraints(&self) -> &[TokenTree] {
        self.path_constraints.as_ref()
    }
}

impl ExecutionEnv {
    pub fn new() -> Self {
        Self::default()
    }

    fn convert_list(&mut self, kind: ListKind, items: &[Expr]) -> TokenTree {
        if let Some((first, rest)) = items.split_first() {
            TokenTree::List {
                kind,
                head: Box::new(self.convert_expr_internal(first)),
                tail: Box::new(self.convert_list(kind, rest)),
            }
        } else {
            TokenTree::Nil
        }
    }

    pub fn add_type(&mut self, name: impl Into<String>, tt: Vec<TokenTree>) {
        self.types.insert(name.into(), tt);
    }

    pub fn fresh_var(&mut self) -> VarId {
        let id = self.var_ids.get(String::from("fresh_var"));
        self.var_ids.reset_scope();
        id
    }

    pub fn convert_expr(&mut self, expr: &Expr) -> TokenTree {
        let mut result = self.convert_expr_internal(expr);
        self.var_ids.reset_scope();
        result.reduce();

        result
    }

    fn convert_expr_internal(&mut self, expr: &Expr) -> TokenTree {
        match expr {
            Expr::Parens(inner) => self.convert_expr_internal(inner),
            Expr::Var(var) => TokenTree::Var(self.var_ids.get(var.as_str().to_string())),
            Expr::TraceCons {
                head,
                tail,
            } => TokenTree::List {
                kind: ListKind::Trace,
                head: Box::new(self.convert_expr_internal(head)),
                tail: Box::new(self.convert_expr_internal(tail)),
            },
            Expr::Compose(items) => self.convert_list(ListKind::Compose, items),
            Expr::ExecInstr {
                instr,
                operands,
            } => TokenTree::Fun {
                name: String::from("execinstr"),
                args: vec![
                    {
                        let name = match &**instr {
                            Expr::Var(name) => name,
                            Expr::Typed {
                                expr, ..
                            } => {
                                if let Expr::Var(name) = &**expr {
                                    name
                                } else {
                                    unimplemented!()
                                }
                            },
                            _ => unimplemented!(),
                        };

                        TokenTree::String(name.as_str().to_string())
                    },
                    self.convert_expr_internal(operands),
                ],
            },
            Expr::List(items) => self.convert_list(ListKind::Comma, items),
            Expr::ListNil(_) => TokenTree::Nil,
            Expr::KNil => TokenTree::Nil,
            Expr::Anything => TokenTree::Anything,
            Expr::Fun {
                name,
                args,
            } => TokenTree::Fun {
                name: name.as_str().to_string(),
                args: args.iter().map(|arg| self.convert_expr_internal(arg)).collect(),
            },
            Expr::Map {
                from,
                to,
            } => TokenTree::MapTo {
                from: Box::new(self.convert_expr_internal(from)),
                to: Box::new(self.convert_expr_internal(to)),
            },
            Expr::String(s) => TokenTree::String(s.clone()),
            Expr::Num(n) => TokenTree::Num(*n),
            Expr::Hex(n) => TokenTree::Hex(*n),
            Expr::UnOp {
                op,
                val,
            } => TokenTree::Fun {
                name: String::from(match op {
                    UnOp::NotBool => "__not_bool",
                }),
                args: vec![self.convert_expr_internal(val)],
            },
            Expr::BinOp {
                lhs,
                op,
                rhs,
            } => TokenTree::Fun {
                name: String::from(match op {
                    BinOp::EqBool => "__eq_bool",
                    BinOp::EqInt => "__eq_int",

                    BinOp::AddInt => "__add_int",
                    BinOp::SubInt => "__sub_int",
                    BinOp::MulInt => "__mul_int",
                    BinOp::Add => "__add",

                    BinOp::XorBool => "__xor_bool",
                    BinOp::AndBool => "__and_bool",
                    BinOp::OrBool => "__or_bool",
                }),
                args: vec![self.convert_expr_internal(lhs), self.convert_expr_internal(rhs)],
            },
            Expr::Typed {
                expr,
                ty,
            } => {
                if let Some(ty) = self.types.get(ty.as_str()) {
                    TokenTree::Typed {
                        ty: Ty(ty.clone()),
                        expr: Box::new(self.convert_expr_internal(expr)),
                    }
                } else {
                    self.convert_expr_internal(expr)
                }
            },
            Expr::Cast {
                expr,
                ty: _,
            } => self.convert_expr_internal(expr),
            Expr::Ite {
                condition,
                then,
                otherwise,
            } => TokenTree::Fun {
                name: String::from("ite"),
                args: vec![
                    self.convert_expr_internal(condition),
                    self.convert_expr_internal(then),
                    self.convert_expr_internal(otherwise),
                ],
            },
            Expr::Lookup {
                expr,
                key,
            } => TokenTree::Fun {
                name: String::from("__lookup"),
                args: vec![self.convert_expr_internal(expr), self.convert_expr_internal(key)],
            },
            Expr::Dollarydoo => TokenTree::Dollarydoo,
        }
    }

    pub fn add_rule(&mut self, rule: &KRule) {
        trace!("Adding rule: {rule:?}");

        // TODO: Also use requires
        let mut vars_bound_by_from = Vec::new();
        let mut vars_needed_in_to = Vec::new();
        let rewrites = rule
            .cells
            .iter()
            .map(|cell| {
                let id = self.cell_ids.get(cell.name.as_str().to_string());
                let mut from = self.convert_expr_internal(&cell.rewrite.from);
                let mut to = cell.rewrite.to.as_ref().map(|to| self.convert_expr_internal(to));
                from.reduce();
                if let Some(to) = &mut to {
                    to.reduce();
                    to.collect_varids(&mut vars_needed_in_to);
                }

                from.collect_varids(&mut vars_bound_by_from);
                // TODO:

                (
                    id,
                    TokenRewrite {
                        from,
                        to,
                        framing: Framing {
                            allow_after: cell.allow_after,
                            allow_before: cell.allow_before,
                        },
                    },
                )
            })
            .collect::<IndexMap<_, _>>();

        let requires = rule
            .requires
            .iter()
            .map(|condition| {
                let mut condition = self.convert_expr_internal(condition);
                condition.reduce();
                condition.collect_varids(&mut vars_needed_in_to);

                condition
            })
            .collect::<Vec<_>>();

        vars_needed_in_to.retain(|var| !vars_bound_by_from.contains(var));
        vars_needed_in_to.sort();
        vars_needed_in_to.dedup();
        if !vars_needed_in_to.is_empty() {
            panic!(
                "Unbound variables in rewrites: {rewrites:#?}\nVariables: {:#?}\nUnbound: {:#?}",
                self.var_ids, vars_needed_in_to
            );
        }

        debug!("Adding rule {rewrites:#?}, var_names={:?}", self.var_ids);
        debug!("Vars bound: {vars_bound_by_from:?}");

        let item = TokenRule {
            rewrites,
            requires,
        };

        if rule.requires.is_empty() {
            self.rules.push(item);
        } else {
            self.conditional_rules.push(item);
        }

        self.var_ids.reset_scope();
    }

    pub fn add_declarations(&mut self, declarations: &[Declaration]) {
        for def in declarations.iter() {
            match def {
                Declaration::Requires(_) => (),
                Declaration::Module {
                    body, ..
                } => {
                    for stmt in body.iter() {
                        match stmt {
                            Statement::Imports(_) => (),
                            Statement::Rule(rule) => {
                                self.add_rule(rule);
                            },
                            Statement::Context => (),
                        }
                    }
                },
            }
        }
    }

    pub fn var_id(&mut self, name: String) -> VarId {
        self.var_ids.get(name)
    }

    pub fn with_cell(mut self, cell_name: String, state: CellState) -> Self {
        let id = self.cell_ids.get(cell_name);

        self.initial_state.cells[id] = Some(state);
        self
    }

    pub fn eval(&mut self) -> Vec<ExecutionState> {
        // Fill all cells used in rules
        let mut state = self.initial_state.clone();
        for rule in self.rules.iter() {
            for cell_id in rule.rewrites.keys() {
                let item = state.cells.get_mut(cell_id);
                if item.is_none() {
                    *item = Some(CellState {
                        tokens: TokenTree::Var(self.var_ids.get(format!(":{}:", cell_id.as_index()))),
                    });
                }

                item.as_mut().unwrap().tokens.reduce();
            }
        }

        let mut num_steps = 0;
        info!("Rewriting {:#?}", self.initial_state.cells);

        let mut result_states = Vec::new();
        let mut pending_states = vec![self.initial_state.clone()];

        while let Some(mut current_state) = pending_states.pop() {
            loop {
                if Self::apply_first_matching_rule(&self.rules, &mut current_state.cells) {
                    for cell in current_state.cells.values_mut() {
                        cell.tokens.reduce();
                    }

                    debug!("Current state: {:#?}", current_state);
                    num_steps += 1;
                    if num_steps >= 100_000 {
                        println!("Rewriting is taking a long time; Current state: {:#?}", current_state.cells)
                    }
                } else {
                    let new_states = Self::apply_conditional_rules(&self.rules, &self.conditional_rules, &current_state);
                    if new_states.is_empty() {
                        info!("State is done: {current_state:#?}");
                        for _ in 0..1000 {
                            for (_, cell) in current_state.cells.iter_mut() {
                                cell.tokens.reduce();
                            }
                        }

                        result_states.push(current_state);
                    } else {
                        pending_states.extend(new_states);
                    }

                    break
                }
            }
        }

        result_states
    }

    fn find_rule_matches<'a>(
        rule: &'a TokenRule, cell_state: &'a mut IndexMap<CellId, CellState>,
    ) -> Option<(IndexMap<VarId, TokenTree>, Vec<PendingRewrite<'a>>)> {
        trace!("Checking rule {rule:#?}");
        let mut mapping = IndexMap::new();
        let checks = rule
            .rewrites
            .iter_all()
            .zip_longest(cell_state.iter_all_mut())
            .map(|item| match item {
                EitherOrBoth::Both((_, None), (..)) => Some(None),
                EitherOrBoth::Both((rule_cell_id, Some(rule_tt)), (cell_id, cell_tt)) => {
                    assert_eq!(rule_cell_id, cell_id);

                    trace!("Check: {rule_tt:?} vs {cell_tt:?}");

                    let cell_tt = &mut cell_tt.unwrap().tokens;

                    trace!("Finding match between:\n    - {cell_tt:?}\n    - {:?}", rule_tt.from);

                    let (tt, map) = cell_tt.find_match(&rule_tt.from, &mapping, &rule_tt.framing)?;
                    mapping = map;
                    if let Some(to) = rule_tt.to.as_ref() {
                        Some(Some(PendingRewrite {
                            tt,
                            to,
                        }))
                    } else {
                        Some(None)
                    }
                },
                EitherOrBoth::Left(_) => unreachable!("self.cell_state was filled at the start of this function"),
                EitherOrBoth::Right((..)) => Some(None),
            });

        let mut matches = Vec::new();
        for check in checks {
            match check {
                Some(Some(rewrite)) => matches.push(rewrite),
                Some(None) => (),
                None => return None,
            }
        }

        Some((mapping, matches))
    }

    fn apply_rewrites(matches: Vec<PendingRewrite<'_>>, mapping: IndexMap<VarId, TokenTree>) {
        for pending in matches {
            let mut new = pending.to.clone();
            new.substitute(&mapping);
            debug!("{:?} => {:?}", pending.tt, new);

            if *pending.tt == new {
                panic!("Made no progress applying rule with {pending:#?}, mapping={mapping:#?}, new={new:#?}");
            }

            *pending.tt = new;
        }
    }

    fn apply_first_matching_rule(rules: &[TokenRule], cell_state: &mut IndexMap<CellId, CellState>) -> bool {
        for rule in rules.iter() {
            if let Some((mapping, matches)) = Self::find_rule_matches(rule, cell_state) {
                if !matches.is_empty() {
                    debug!("Applying {rule:#?}");
                    assert!(rule.requires.is_empty());

                    Self::apply_rewrites(matches, mapping);

                    return true
                }
            }
        }

        false
    }

    fn apply_conditional_rules(
        rules: &[TokenRule], conditional_rules: &[TokenRule], cell_state: &ExecutionState,
    ) -> Vec<ExecutionState> {
        let mut result = Vec::new();
        for rule in conditional_rules.iter() {
            let mut state = cell_state.clone();
            if let Some((mapping, matches)) = Self::find_rule_matches(rule, &mut state.cells) {
                if !matches.is_empty() {
                    debug!("Applying {rule:#?}");
                    assert!(!rule.requires.is_empty());

                    let conditions = rule.requires.iter().map(|condition| {
                        let mut tt = condition.clone();
                        tt.substitute(&mapping);
                        tt.reduce();
                        // !! Hacky solution; Re-uses the k-cell to reduce the condition
                        let mut cells = cell_state.cells.clone();
                        cells[CellId::from_usize(1)] = Some(CellState {
                            tokens: tt,
                        });

                        info!("Reducing condition: {cells:#?}");
                        while Self::apply_first_matching_rule(rules, &mut cells) {
                            for cell in cells.values_mut() {
                                cell.tokens.reduce();
                            }

                            debug!("Current state: {:#?}", cells);
                        }

                        cells[CellId::from_usize(1)].clone().unwrap().tokens
                    });
                    state.path_constraints.extend(conditions);

                    Self::apply_rewrites(matches, mapping);
                    result.push(state);
                }
            }
        }

        result
    }

    // pub fn get_cell(&mut self, arg: &str) -> Option<&TokenTree> {
    //     self.initial_state.cells[self.cell_ids.get(arg.to_string())].as_ref().map(|cell| &cell.tokens)
    // }

    pub fn get_state_cell<'a>(&mut self, state: &'a ExecutionState, arg: &str) -> Option<&'a TokenTree> {
        state.cells[self.cell_ids.get(arg.to_string())]
            .as_ref()
            .map(|cell| &cell.tokens)
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use super::{CellState, ExecutionEnv, ListKind, TokenTree};
    use crate::ast::{parse_rewrite, Cell, Ident, KRule};

    #[test]
    pub fn apply_transitions() {
        let mut env = ExecutionEnv::new();

        env.add_rule(&KRule {
            cells: vec![Cell {
                name: Ident::from("k"),
                rewrite: parse_rewrite("add(a, s(b)) => add(s(a), b)").unwrap(),
                allow_after: true,
                allow_before: true,
            }],
            requires: Vec::new(),
        });

        fn s(tt: TokenTree) -> TokenTree {
            TokenTree::Fun {
                name: String::from("s"),
                args: vec![tt],
            }
        }
        fn add(lhs: TokenTree, rhs: TokenTree) -> TokenTree {
            TokenTree::Fun {
                name: String::from("add"),
                args: vec![lhs, rhs],
            }
        }

        let [x, y] = ["x", "y"].map(|name| env.var_ids.get(String::from(name))).map(TokenTree::Var);

        let mut env = env.with_cell(
            String::from("k"),
            CellState {
                tokens: add(x.clone(), s(s(s(y.clone())))),
            },
        );

        let result = env.eval();
        assert_eq!(result.len(), 1);

        assert_eq!(env.get_state_cell(&result[0], "k").unwrap(), &add(s(s(s(x))), y));
    }

    #[test]
    pub fn var_binding_with_multiple_cells() {
        let mut env = ExecutionEnv::new();

        env.add_rule(&KRule {
            cells: vec![
                Cell {
                    name: Ident::from("k"),
                    rewrite: parse_rewrite("add(n) => .").unwrap(),
                    allow_after: true,
                    allow_before: true,
                },
                Cell {
                    name: Ident::from("j"),
                    rewrite: parse_rewrite("k => add(k, n)").unwrap(),
                    allow_after: true,
                    allow_before: true,
                },
            ],
            requires: Vec::new(),
        });

        fn add(args: &[TokenTree]) -> TokenTree {
            TokenTree::Fun {
                name: String::from("add"),
                args: args.to_vec(),
            }
        }

        let [x, y] = ["x", "y"].map(|name| env.var_ids.get(String::from(name))).map(TokenTree::Var);

        let mut env = env
            .with_cell(
                String::from("k"),
                CellState {
                    tokens: add(&[x.clone()]),
                },
            )
            .with_cell(
                String::from("j"),
                CellState {
                    tokens: y.clone(),
                },
            );

        let result = env.eval();
        assert_eq!(result.len(), 1);

        assert_eq!(env.get_state_cell(&result[0], "k").unwrap(), &TokenTree::Nil);
        assert_eq!(env.get_state_cell(&result[0], "j").unwrap(), &add(&[y, x]));
    }

    #[test]
    pub fn test_map_update() {
        fn f(s: impl Into<String>, args: &[TokenTree]) -> TokenTree {
            TokenTree::Fun {
                name: s.into(),
                args: args.to_vec(),
            }
        }
        fn l(head: TokenTree, tail: TokenTree) -> TokenTree {
            TokenTree::List {
                kind: ListKind::Compose,
                head: Box::new(head),
                tail: Box::new(tail),
            }
        }
        fn lc(head: TokenTree, tail: TokenTree) -> TokenTree {
            TokenTree::List {
                kind: ListKind::Comma,
                head: Box::new(head),
                tail: Box::new(tail),
            }
        }
        fn m(s: impl Into<String>, to: TokenTree) -> TokenTree {
            TokenTree::MapTo {
                from: Box::new(TokenTree::String(s.into())),
                to: Box::new(to),
            }
        }

        let mut e = f(
            "updateMap",
            &[
                l(
                    m("a", TokenTree::Num(0)),
                    l(m("b", TokenTree::Num(1)), m("c", TokenTree::Num(2))),
                ),
                m("b", TokenTree::Num(5)),
            ],
        );

        println!("{e:#?}");

        assert!(e.reduce());

        println!("{e:#?}");

        assert_eq!(
            e,
            lc(
                m("a", TokenTree::Num(0)),
                lc(m("b", TokenTree::Num(5)), lc(m("c", TokenTree::Num(2)), TokenTree::Nil,),)
            )
        );
    }

    #[test]
    pub fn test_fix_list() {
        fn l(head: TokenTree, tail: TokenTree) -> TokenTree {
            TokenTree::List {
                kind: ListKind::Comma,
                head: Box::new(head),
                tail: Box::new(tail),
            }
        }

        let mut e = l(l(TokenTree::Num(1), TokenTree::Num(2)), TokenTree::Num(0));

        println!("{e:#?}");

        assert!(e.reduce());

        println!("{e:#?}");

        assert_eq!(e, l(TokenTree::Num(1), l(TokenTree::Num(2), TokenTree::Num(0),),));
    }
}
