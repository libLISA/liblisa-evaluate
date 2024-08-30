use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::Debug;
use std::ops::Not;

use itertools::Itertools;
use lazy_static::lazy_static;
use liblisa::smt::{Dynamic, SmtBV, SmtBool, SmtInt, SmtSolver, SortKind};
use log::{debug, error, info, trace};
use serde::{Deserialize, Serialize};

use crate::ast::{parse, Declaration, Expr};
use crate::rewrite::{CellState, ExecutionEnv, ListKind, TokenTree};

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Z3Fun {
    Eq,
    Concat,
    Extract {
        hi: u32,
        lo: u32,
    },
    DynamicExtract,
    MakeBvWithDynamicSize,
    SignExtend(u32),
    MakeBvWithSize(u32),
    Ite,
    Add,
    Mul,
    Sub,
    And,
    Xor,
    Or,
    Not,
    BvSignedGt,
    BvSignedLt,
    BvUnsignedGt,
    BvUnsignedLt,
    BvUnsignedLe,
    BvUnsignedGe,

    BvToSignedInt,
    BvToUnsignedInt,

    BvLshr,
    #[serde(alias = "BvAshl")]
    BvAshr,
    BvShl,
    BvAdd,
    BvXor,
    BvAnd,
    BvOr,
    BvSub,
    BvMul,
    BvRol,
    BvRor,
    FpFunc,

    BvScanReverse,
    BvScanForward,

    BvPopCount,

    #[serde(alias = "BvNeg")]
    BvNot,
    BvUnsignedRem,

    PlugInMask,

    Pdep32,
    Pdep64,
    Pextr32,
    Pextr64,

    UnsignedRem(u8),
    SignedRem(u8),
    UnsignedDiv(u8),
    SignedDiv(u8),

    BvBitSize,

    SameRegisters,
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Z3Node {
    Var(String),
    Memory { computation: Box<Z3Node>, size: u32 },
    IntConst(i128),
    BvConst { val: i128, size: u32 },
    Fun { name: Z3Fun, args: Vec<Z3Node> },
    BoolConst(bool),
    BoolUndef,
    MIntUndef(usize),
    Imm(usize),
    Unsupported,
    OriginalValue(Box<Z3Node>),
    InstructionByteLength,
}

impl Debug for Z3Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Z3Node::Var(v) => write!(f, "{v}"),
            Z3Node::Fun {
                name,
                args,
            } => write!(f, "({name:?} {:?})", args.iter().format(" ")),
            Z3Node::IntConst(n) => write!(f, "{n}"),
            Z3Node::BvConst {
                val,
                size,
            } => write!(f, "#x{val:X}:{size}"),
            Z3Node::BoolConst(b) => write!(f, "{b}"),
            Z3Node::BoolUndef => write!(f, "undefBool"),
            Z3Node::MIntUndef(n) => write!(f, "undefInt{n}"),
            Z3Node::Memory {
                computation,
                size,
            } => write!(f, "mem[{computation:?}]:{size}"),
            Z3Node::Imm(n) => write!(f, "Imm{n}"),
            Z3Node::Unsupported => write!(f, "<not supported>"),
            Z3Node::OriginalValue(node) => write!(f, "OriginalValue({node:?})"),
            Z3Node::InstructionByteLength => write!(f, "InstructionByteLength"),
        }
    }
}

pub trait Kz3Converter<'ctx, S: SmtSolver<'ctx>> {
    fn var(&mut self, context: &mut S, name: &str) -> Dynamic<'ctx, S>;
    fn mem(&mut self, context: &mut S, computation: &Z3Node, size: u32) -> Dynamic<'ctx, S>;
    fn undef_bool(&mut self, context: &mut S) -> S::Bool;
    fn undef_bv(&mut self, context: &mut S, size: usize) -> S::BV;
    fn imm(&mut self, context: &mut S, n: usize) -> S::BV;
    fn instruction_byte_length(&self) -> usize;
}

fn to_int<'ctx, S: SmtSolver<'ctx>>(context: &mut S, v: Dynamic<'ctx, S>) -> u64 {
    match v {
        Dynamic::BV(v) => {
            let v = context.int_from_bv(v, false).simplify();
            let Some(v) = v.clone().as_u64() else {
                error!("Unable to extract int from {v:?}");
                return 1
            };

            v
        },
        Dynamic::Int(v) => {
            let v = v.simplify();
            let Some(v) = v.clone().as_u64() else {
                error!("Unable to extract int from {v:?}");
                return 1
            };

            v
        },
        v => {
            error!("Unable to extract int from {v:?}");
            return 1
        },
    }
}

fn undef_if_zero<'ctx, S: SmtSolver<'ctx>>(
    context: &mut S, conv: &mut impl Kz3Converter<'ctx, S>, result: S::BV, maybe_zero: S::BV,
) -> S::BV {
    let is_zero = maybe_zero.clone()._eq(context.bv_from_u64(0, maybe_zero.get_size()));

    is_zero.ite_bv(conv.undef_bv(context, result.get_size() as usize), result)
}

impl Z3Node {
    fn make_bv<'ctx, S: SmtSolver<'ctx>>(
        &self, context: &mut S, conv: &mut impl Kz3Converter<'ctx, S>, target_size: u32,
    ) -> Dynamic<'ctx, S> {
        if let Z3Node::Fun {
            name: Z3Fun::BvToSignedInt,
            args,
        } = self
        {
            let v = args[0].smt(context, conv).as_bv().unwrap();
            let original_size = v.get_size();

            Dynamic::from_bv(v.sign_ext(target_size - original_size))
        } else {
            let v = self.smt(context, conv);
            match v.sort_kind() {
                SortKind::Int => Dynamic::from_bv(context.bv_from_int(v.as_int().unwrap(), target_size)),
                SortKind::BV => {
                    let v = v.as_bv().unwrap();
                    let current_size = v.get_size();
                    Dynamic::from_bv(match current_size.cmp(&target_size) {
                        Ordering::Less => v.zero_ext(target_size - current_size),
                        Ordering::Greater => v.extract(target_size - 1, 0),
                        Ordering::Equal => v,
                    })
                },
                other => unimplemented!("Conversion from {other:?} to BV"),
            }
        }
    }

    fn smt_expect_bv<'ctx, S: SmtSolver<'ctx>>(
        &self, context: &mut S, conv: &mut impl Kz3Converter<'ctx, S>, expected_size: u32,
    ) -> S::BV {
        match self {
            Z3Node::Fun {
                name: Z3Fun::BvToUnsignedInt,
                args,
            } => {
                let bv = args[0].smt(context, conv).as_bv().unwrap();
                let bv_size = bv.get_size();
                if bv_size < expected_size {
                    bv.zero_ext(expected_size - bv_size)
                } else {
                    bv
                }
            },
            Z3Node::Fun {
                name: Z3Fun::BvToSignedInt,
                args,
            } => {
                let bv = args[0].smt(context, conv).as_bv().unwrap();
                let bv_size = bv.get_size();
                if bv_size < expected_size {
                    bv.sign_ext(expected_size - bv_size)
                } else {
                    bv
                }
            },
            _ => {
                let val = self.smt(context, conv);
                match val.sort_kind() {
                    SortKind::BV => {
                        let val = val.as_bv().unwrap();
                        assert_eq!(val.get_size(), expected_size);
                        val
                    },
                    SortKind::Int => context.bv_from_int(val.as_int().unwrap(), expected_size),
                    kind => unimplemented!("{kind:?} as BV of size {expected_size}"),
                }
            },
        }
    }

    pub fn smt<'ctx, S: SmtSolver<'ctx>>(&self, context: &mut S, conv: &mut impl Kz3Converter<'ctx, S>) -> Dynamic<'ctx, S> {
        match self {
            Z3Node::Var(var) => conv.var(context, var),
            Z3Node::Memory {
                computation,
                size,
            } => conv.mem(context, computation, *size),
            Z3Node::IntConst(i) => context.int_from_i64((*i).try_into().unwrap()).into_dynamic(),
            Z3Node::BvConst {
                val,
                size,
            } => Dynamic::from_bv(context.bv_from_u64((*val).try_into().unwrap(), *size)),
            Z3Node::Fun {
                name,
                args,
            } => {
                match name {
                    Z3Fun::Eq => {
                        let lhs = args[0].smt(context, conv);
                        let rhs = args[1].smt(context, conv);

                        trace!("Comparing sorts {:?} vs {:?}", lhs.sort(), rhs.sort());
                        if lhs.sort_kind() == rhs.sort_kind() && lhs.sort() == rhs.sort() {
                            lhs._eq(rhs).into_dynamic()
                        } else {
                            debug!(
                                "WARNING: treating comparison between {lhs:?} and {rhs:?} as always false, because sorts differ!"
                            );
                            context.bool_from_bool(false).into_dynamic()
                        }
                    },
                    Z3Fun::Concat => {
                        assert_eq!(args.len(), 2);
                        Dynamic::from_bv(
                            args[0]
                                .smt(context, conv)
                                .as_bv()
                                .unwrap()
                                .concat(args[1].smt(context, conv).as_bv().unwrap()),
                        )
                    },
                    // TODO: Seems like 16:8 is supposed to mean (BITVEC_WIDTH - 8 - 1):(BITVEC_WIDTH-16)
                    Z3Fun::Extract {
                        hi,
                        lo,
                    } => {
                        let bv = &args[0].smt(context, conv).as_bv().unwrap();
                        let bits = bv.get_size();
                        assert!(*lo < bits && *hi <= bits, "extract {hi}:{lo} not within {bits} of {bv}");
                        let real_hi = bits - *lo - 1;
                        let real_lo = bits - *hi;

                        trace!("Extract {hi}:{lo} in {bits} bits => extract {real_hi}:{real_lo}");

                        Dynamic::from_bv(bv.clone().extract(real_hi, real_lo))
                    },
                    Z3Fun::DynamicExtract => {
                        let bv = args[0].smt(context, conv).as_bv().unwrap();
                        let lo = args[1].smt(context, conv);
                        let lo = to_int(context, lo) as u32;
                        let hi = args[2].smt(context, conv);
                        let hi = to_int(context, hi) as u32;

                        let bits = bv.get_size();
                        let real_hi = bits - lo - 1;
                        let real_lo = bits - hi;

                        trace!("Extract {hi}:{lo} in {bits} bits => extract {real_hi}:{real_lo}");

                        if real_hi >= real_lo {
                            assert!(real_hi < bv.get_size());

                            Dynamic::from_bv(bv.extract(real_hi, real_lo))
                        } else {
                            error!("Extract {hi}:{lo} in {bits} bits => extract {real_hi}:{real_lo} source: {self:?}");
                            Dynamic::from_bv(context.new_bv_const("conversion_error", real_lo - real_hi))
                        }
                    },
                    Z3Fun::BvToSignedInt => match &args[0] {
                        Z3Node::BvConst {
                            val,
                            size,
                        } if (*val as i64 as i128) == *val => context
                            .int_from_i64(i64::try_from((val << (128 - size)) >> (128 - size)).unwrap())
                            .into_dynamic(),
                        arg => {
                            let bv = arg.smt(context, conv).as_bv().unwrap();
                            trace!("Converting {arg:?} / {bv} to signed int");
                            context.int_from_bv(bv, true).into_dynamic()
                        },
                    },
                    Z3Fun::BvToUnsignedInt => match &args[0] {
                        Z3Node::BvConst {
                            val,
                            size,
                        } if (*val as u64 as i128) == *val => context
                            .int_from_u64(u64::try_from(((*val as u128) << (128 - size)) >> (128 - size)).unwrap())
                            .into_dynamic(),
                        arg => {
                            let bv = arg.smt(context, conv).as_bv().unwrap();
                            trace!("Converting {arg:?} / {bv} to unsigned int");
                            context.int_from_bv(bv, false).into_dynamic()
                        },
                    },
                    Z3Fun::MakeBvWithSize(target_size) => args[0].make_bv(context, conv, *target_size),
                    Z3Fun::MakeBvWithDynamicSize => {
                        let target_size = args[0].smt(context, conv).simplify();
                        let target_size = to_int(context, target_size) as u32;

                        args[1].make_bv(context, conv, target_size)
                    },
                    Z3Fun::SignExtend(n) => {
                        let val = args[0].smt(context, conv).as_bv().unwrap();
                        let get_size = val.get_size();
                        Dynamic::from_bv(val.sign_ext(*n - get_size))
                    },
                    Z3Fun::Ite => {
                        let cond = args[0].smt(context, conv).as_bool().unwrap();
                        if let Some(result) = cond.clone().simplify().as_bool() {
                            trace!("Can solve {cond} ({:?}) = {result}", args[0]);
                            if result {
                                args[1].smt(context, conv)
                            } else {
                                args[2].smt(context, conv)
                            }
                        } else {
                            let a = args[1].smt(context, conv);
                            let b = args[2].smt(context, conv);

                            assert_eq!(a.sort(), b.sort(), "both branches of ITE must have same sort: {a:?} {b:?}");
                            cond.ite_dynamic(a, b)
                        }
                    },
                    Z3Fun::Add => (args[0].smt(context, conv).as_int().unwrap() + args[1].smt(context, conv).as_int().unwrap())
                        .into_dynamic(),
                    Z3Fun::Mul => (args[0].smt(context, conv).as_int().unwrap() * args[1].smt(context, conv).as_int().unwrap())
                        .into_dynamic(),
                    Z3Fun::Sub => (args[0].smt(context, conv).as_int().unwrap() - args[1].smt(context, conv).as_int().unwrap())
                        .into_dynamic(),
                    Z3Fun::And => (args[0].smt(context, conv).as_bool().unwrap() & args[1].smt(context, conv).as_bool().unwrap())
                        .into_dynamic(),
                    Z3Fun::Xor => (args[0].smt(context, conv).as_bool().unwrap() ^ args[1].smt(context, conv).as_bool().unwrap())
                        .into_dynamic(),
                    Z3Fun::Or => (args[0].smt(context, conv).as_bool().unwrap() | args[1].smt(context, conv).as_bool().unwrap())
                        .into_dynamic(),
                    Z3Fun::Not => {
                        let val = args[0].smt(context, conv);
                        match val.sort_kind() {
                            SortKind::BV => val.as_bv().unwrap().not().into_dynamic(),
                            SortKind::Bool => val.as_bool().unwrap().not().into_dynamic(),
                            kind => unimplemented!("not({kind:?})"),
                        }
                    },
                    Z3Fun::BvSignedGt => args[0]
                        .smt(context, conv)
                        .as_bv()
                        .unwrap()
                        .bvsgt(args[1].smt(context, conv).as_bv().unwrap())
                        .into_dynamic(),
                    Z3Fun::BvSignedLt => args[0]
                        .smt(context, conv)
                        .as_bv()
                        .unwrap()
                        .bvslt(args[1].smt(context, conv).as_bv().unwrap())
                        .into_dynamic(),
                    Z3Fun::BvUnsignedGt => args[0]
                        .smt(context, conv)
                        .as_bv()
                        .unwrap()
                        .bvugt(args[1].smt(context, conv).as_bv().unwrap())
                        .into_dynamic(),
                    Z3Fun::BvUnsignedLt => args[0]
                        .smt(context, conv)
                        .as_bv()
                        .unwrap()
                        .bvult(args[1].smt(context, conv).as_bv().unwrap())
                        .into_dynamic(),
                    Z3Fun::BvUnsignedLe => args[0]
                        .smt(context, conv)
                        .as_bv()
                        .unwrap()
                        .bvule(args[1].smt(context, conv).as_bv().unwrap())
                        .into_dynamic(),
                    Z3Fun::BvUnsignedGe => args[0]
                        .smt(context, conv)
                        .as_bv()
                        .unwrap()
                        .bvuge(args[1].smt(context, conv).as_bv().unwrap())
                        .into_dynamic(),
                    Z3Fun::BvLshr => {
                        let lhs = args[0].smt(context, conv).as_bv().unwrap();
                        let rhs = args[1].smt_expect_bv(context, conv, lhs.get_size());
                        lhs.bvlshr(rhs).into_dynamic()
                    },
                    Z3Fun::BvAshr => {
                        let lhs = args[0].smt(context, conv).as_bv().unwrap();
                        let rhs = args[1].smt_expect_bv(context, conv, lhs.get_size());
                        lhs.bvashr(rhs).into_dynamic()
                    },
                    Z3Fun::BvShl => {
                        let lhs = args[0].smt(context, conv).as_bv().unwrap();
                        let rhs = args[1].smt_expect_bv(context, conv, lhs.get_size());
                        lhs.bvshl(rhs).into_dynamic()
                    },
                    Z3Fun::BvAdd => {
                        let lhs = args[0].smt(context, conv).as_bv().unwrap();
                        let rhs = args[1].smt(context, conv).as_bv().unwrap();
                        assert_eq!(
                            lhs.get_size(),
                            rhs.get_size(),
                            "Mismatched BV sizes in {self:?} // {lhs} vs {rhs}"
                        );
                        Dynamic::from_bv(lhs + rhs)
                    },
                    Z3Fun::BvXor => Dynamic::from_bv(
                        args[0].smt(context, conv).as_bv().unwrap() ^ args[1].smt(context, conv).as_bv().unwrap(),
                    ),
                    Z3Fun::BvAnd => Dynamic::from_bv(
                        args[0].smt(context, conv).as_bv().unwrap() & args[1].smt(context, conv).as_bv().unwrap(),
                    ),
                    Z3Fun::BvOr => Dynamic::from_bv(
                        args[0].smt(context, conv).as_bv().unwrap() | args[1].smt(context, conv).as_bv().unwrap(),
                    ),
                    Z3Fun::BvSub => Dynamic::from_bv(
                        args[0].smt(context, conv).as_bv().unwrap() - args[1].smt(context, conv).as_bv().unwrap(),
                    ),
                    Z3Fun::BvMul => Dynamic::from_bv(
                        args[0].smt(context, conv).as_bv().unwrap() * args[1].smt(context, conv).as_bv().unwrap(),
                    ),
                    Z3Fun::BvRol => Dynamic::from_bv(
                        args[0]
                            .smt(context, conv)
                            .as_bv()
                            .unwrap()
                            .bvrotl(args[1].smt(context, conv).as_bv().unwrap()),
                    ),
                    Z3Fun::BvRor => Dynamic::from_bv(
                        args[0]
                            .smt(context, conv)
                            .as_bv()
                            .unwrap()
                            .bvrotr(args[1].smt(context, conv).as_bv().unwrap()),
                    ),
                    Z3Fun::FpFunc => todo!("FpFunc"),
                    Z3Fun::BvNot => Dynamic::from_bv(args[0].smt(context, conv).as_bv().unwrap().not()),
                    Z3Fun::BvUnsignedRem => Dynamic::from_bv(
                        args[0]
                            .smt(context, conv)
                            .as_bv()
                            .unwrap()
                            .bvurem(args[1].smt(context, conv).as_bv().unwrap()),
                    ),
                    Z3Fun::PlugInMask => {
                        let target = args[0].smt(context, conv).as_bv().unwrap();
                        let plug = args[1].smt(context, conv).as_bv().unwrap();
                        let pos = args[2].smt(context, conv);
                        let pos = to_int(context, pos) as u32;

                        trace!("PlugInMask({target:?}, {plug:?}, {pos})");

                        let hi = target.get_size() - 1;
                        let mid_hi = pos + plug.get_size();
                        if pos == 0 {
                            target.clone().extract(hi, mid_hi).concat(plug).into_dynamic()
                        } else {
                            let mid_lo = pos - 1;
                            target
                                .clone()
                                .extract(hi, mid_hi)
                                .concat(plug)
                                .concat(target.extract(mid_lo, 0))
                                .into_dynamic()
                        }
                    },
                    Z3Fun::UnsignedRem(num_bits) => {
                        let a = args[0].smt(context, conv).as_bv().unwrap();
                        let b = args[1].smt(context, conv).as_bv().unwrap();
                        trace!("bvurem between {a} and {b}");

                        let a_size = a.get_size();
                        let a = if a_size < 128 { a.zero_ext(128 - a_size) } else { a };

                        let b_size = b.get_size();
                        let b = if b_size < 128 { b.zero_ext(128 - b_size) } else { b };

                        Dynamic::from_bv(undef_if_zero(
                            context,
                            conv,
                            a.bvurem(b.clone()).extract(*num_bits as u32 - 1, 0),
                            b,
                        ))
                    },
                    Z3Fun::SignedRem(num_bits) => {
                        let a = args[0].smt(context, conv).as_bv().unwrap();
                        let b = args[1].smt(context, conv).as_bv().unwrap();
                        trace!("bvsrem between {a} and {b}");

                        let a_size = a.get_size();
                        let a = if a_size < 128 { a.sign_ext(128 - a_size) } else { a };

                        let b_size = b.get_size();
                        let b = if b_size < 128 { b.sign_ext(128 - b_size) } else { b };

                        Dynamic::from_bv(undef_if_zero(
                            context,
                            conv,
                            a.bvsrem(b.clone()).extract(*num_bits as u32 - 1, 0),
                            b,
                        ))
                    },
                    Z3Fun::UnsignedDiv(num_bits) => {
                        let a = args[0].smt(context, conv).as_bv().unwrap();
                        let b = args[1].smt(context, conv).as_bv().unwrap();
                        trace!("bvudiv between {a} and {b}");

                        let a_size = a.get_size();
                        let a = if a_size < 128 { a.zero_ext(128 - a_size) } else { a };

                        let b_size = b.get_size();
                        let b = if b_size < 128 { b.zero_ext(128 - b_size) } else { b };

                        Dynamic::from_bv(undef_if_zero(
                            context,
                            conv,
                            a.bvudiv(b.clone()).extract(*num_bits as u32 - 1, 0),
                            b,
                        ))
                    },
                    Z3Fun::SignedDiv(num_bits) => {
                        let a = args[0].smt(context, conv).as_bv().unwrap();
                        let b = args[1].smt(context, conv).as_bv().unwrap();
                        trace!("bvsdiv between {a} and {b}");

                        let a_size = a.get_size();
                        let a = if a_size < 128 { a.sign_ext(128 - a_size) } else { a };

                        let b_size = b.get_size();
                        let b = if b_size < 128 { b.sign_ext(128 - b_size) } else { b };

                        Dynamic::from_bv(undef_if_zero(
                            context,
                            conv,
                            a.bvsdiv(b.clone()).extract(*num_bits as u32 - 1, 0),
                            b,
                        ))
                    },
                    Z3Fun::BvBitSize => {
                        let val = args[0].smt(context, conv).as_bv().unwrap().get_size() as u64;
                        context.int_from_u64(val).into_dynamic()
                    },
                    Z3Fun::BvPopCount => {
                        let bv = args[0].smt(context, conv).as_bv().unwrap();
                        context.popcount(&bv, bv.get_size()).into_dynamic()
                    },
                    Z3Fun::BvScanReverse => {
                        let bv = args[0].smt(context, conv).as_bv().unwrap();
                        Dynamic::from_bv(context.bv_from_u64(bv.get_size() as u64 - 1, 128) - context.count_leading_zeros(bv))
                    },
                    Z3Fun::BvScanForward => {
                        let bv = args[0].smt(context, conv).as_bv().unwrap();
                        Dynamic::from_bv(context.count_trailing_zeros(bv))
                    },
                    Z3Fun::SameRegisters => {
                        let a = args[0].smt(context, conv);
                        let b = args[1].smt(context, conv);

                        debug!("SameRegisters({a:?}, {b:?})");
                        let is_identical = a.is_identical(&b);
                        debug!("is_identical = {is_identical}");

                        context.bool_from_bool(is_identical).into_dynamic()
                    },
                    Z3Fun::Pdep32 => {
                        let mask = args[0].smt(context, conv).as_bv().unwrap().extract(31, 0).sign_ext(96);
                        let source = args[1].smt(context, conv).as_bv().unwrap().extract(31, 0).sign_ext(96);

                        Dynamic::from_bv(context.deposit_bits::<128>(source, mask).extract(31, 0))
                    },
                    Z3Fun::Pdep64 => {
                        let mask = args[0].smt(context, conv).as_bv().unwrap().extract(63, 0).sign_ext(64);
                        let source = args[1].smt(context, conv).as_bv().unwrap().extract(63, 0).sign_ext(64);

                        Dynamic::from_bv(context.deposit_bits::<128>(source, mask).extract(63, 0))
                    },
                    Z3Fun::Pextr32 => {
                        let mask = args[0].smt(context, conv).as_bv().unwrap().extract(31, 0).zero_ext(96);
                        let source = args[1].smt(context, conv).as_bv().unwrap().extract(31, 0).zero_ext(96);

                        Dynamic::from_bv(context.extract_bits::<128>(source, mask).extract(31, 0))
                    },
                    Z3Fun::Pextr64 => {
                        let mask = args[0].smt(context, conv).as_bv().unwrap().extract(63, 0).zero_ext(64);
                        let source = args[1].smt(context, conv).as_bv().unwrap().extract(63, 0).zero_ext(64);

                        Dynamic::from_bv(context.extract_bits::<128>(source, mask).extract(63, 0))
                    },
                }
            },
            Z3Node::BoolConst(b) => context.bool_from_bool(*b).into_dynamic(),
            Z3Node::BoolUndef => conv.undef_bool(context).into_dynamic(),
            Z3Node::MIntUndef(n) => Dynamic::from_bv(conv.undef_bv(context, *n)),
            Z3Node::Imm(n) => Dynamic::from_bv(conv.imm(context, *n)),
            Z3Node::OriginalValue(node) => node.smt(context, conv),
            Z3Node::Unsupported => panic!("Unsupported"),
            Z3Node::InstructionByteLength => context.bv_from_u64(conv.instruction_byte_length() as u64, 64).into_dynamic(),
        }
    }

    pub fn contains_unsupported(&self) -> bool {
        match self {
            Z3Node::Fun {
                name: Z3Fun::FpFunc, ..
            }
            | Z3Node::Unsupported => true,
            Z3Node::Fun {
                args, ..
            } => args.iter().any(|node| node.contains_unsupported()),
            Z3Node::Memory {
                computation, ..
            } => computation.contains_unsupported(),
            _ => false,
        }
    }

    pub fn is_identity(&self, storage_loc: &StorageLocation) -> bool {
        debug!("Checking identity of {self:?} vs {storage_loc:?}");
        if let Z3Node::Var(var) = self {
            &StorageLocation::Reg(var.strip_prefix("reg_").unwrap_or(var).to_string()) == storage_loc
        } else {
            false
        }
    }

    pub fn substitute_original_value(&self, existing: &Z3Node) -> Z3Node {
        match self {
            Z3Node::Memory {
                computation,
                size,
            } => Z3Node::Memory {
                computation: Box::new(computation.substitute_original_value(existing)),
                size: *size,
            },
            Z3Node::Fun {
                name,
                args,
            } => Z3Node::Fun {
                name: *name,
                args: args.iter().map(|arg| arg.substitute_original_value(existing)).collect(),
            },
            Z3Node::OriginalValue(_) => existing.clone(),
            _ => self.clone(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum StorageLocation {
    Reg(String),
    Mem { offset: Z3Node, size: usize },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Kz3 {
    map: Vec<(StorageLocation, Z3Node)>,
}

impl Kz3 {
    fn make_tt_strings(items: &[&str]) -> Vec<TokenTree> {
        items.iter().map(|item| TokenTree::String(item.to_string())).collect()
    }

    pub fn iter(&self) -> impl Iterator<Item = &(StorageLocation, Z3Node)> {
        self.map.iter()
    }

    pub fn expand(declarations: &[Declaration], op: &TokenTree, operands: &[TokenTree]) -> Option<Self> {
        let mut env = ExecutionEnv::default();
        // TODO: The rest...
        env.add_type(
            "Rh",
            Self::make_tt_strings(&["%ah", "%bh", "%ch", "%dh", "%virt:Rh:0", "%virt:Rh:1", "%virt:Rh:2"]),
        );
        env.add_type(
            "R8",
            Self::make_tt_strings(&[
                "%al",
                "%bl",
                "%cl",
                "%dl",
                "%sil",
                "%dil",
                "%spl",
                "%bpl",
                "%r8b",
                "%r9b",
                "%r10b",
                "%r11b",
                "%r12b",
                "%r13b",
                "%r14b",
                "%r15b",
                "%virt:R8:0",
                "%virt:R8:1",
                "%virt:R8:2",
            ]),
        );
        env.add_type(
            "R16",
            Self::make_tt_strings(&[
                "%ax",
                "%bx",
                "%cx",
                "%dx",
                "%si",
                "%di",
                "%sp",
                "%bp",
                "%r8w",
                "%r9w",
                "%r10w",
                "%r11w",
                "%r12w",
                "%r13w",
                "%r14w",
                "%r15w",
                "%virt:R16:0",
                "%virt:R16:1",
                "%virt:R16:2",
            ]),
        );
        env.add_type(
            "R32",
            Self::make_tt_strings(&[
                "%eax",
                "%ebx",
                "%ecx",
                "%edx",
                "%esi",
                "%edi",
                "%esp",
                "%ebp",
                "%r8d",
                "%r9d",
                "%r10d",
                "%r11d",
                "%r12d",
                "%r13d",
                "%r14d",
                "%r15d",
                "%virt:R32:0",
                "%virt:R32:1",
                "%virt:R32:2",
            ]),
        );
        env.add_type(
            "R64",
            Self::make_tt_strings(&[
                "%rax",
                "%rbx",
                "%rcx",
                "%rdx",
                "%rsi",
                "%rdi",
                "%rsp",
                "%rbp",
                "%r8",
                "%r9",
                "%r10",
                "%r11",
                "%r12",
                "%r13",
                "%r14",
                "%r15",
                "%virt:R64:0",
                "%virt:R64:1",
                "%virt:R64:2",
            ]),
        );
        env.add_type(
            "Xmm",
            Self::make_tt_strings(&[
                "%xmm0",
                "%xmm1",
                "%xmm2",
                "%xmm3",
                "%xmm4",
                "%xmm5",
                "%xmm6",
                "%xmm7",
                "%xmm8",
                "%xmm9",
                "%xmm10",
                "%xmm11",
                "%xmm12",
                "%xmm13",
                "%xmm14",
                "%xmm15",
                "%virt:Xmm:0",
                "%virt:Xmm:1",
                "%virt:Xmm:2",
                "%virt:Xmm:3",
            ]),
        );
        env.add_type(
            "Ymm",
            Self::make_tt_strings(&[
                "%ymm0",
                "%ymm1",
                "%ymm2",
                "%ymm3",
                "%ymm4",
                "%ymm5",
                "%ymm6",
                "%ymm7",
                "%ymm8",
                "%ymm9",
                "%ymm10",
                "%ymm11",
                "%ymm12",
                "%ymm13",
                "%ymm14",
                "%ymm15",
                "%virt:Ymm:0",
                "%virt:Ymm:1",
                "%virt:Ymm:2",
                "%virt:Ymm:3",
            ]),
        );
        env.add_type(
            "Imm",
            vec![
                TokenTree::List {
                    kind: ListKind::Compose,
                    head: Box::new(TokenTree::Dollarydoo),
                    tail: Box::new(TokenTree::Anything),
                },
                TokenTree::List {
                    kind: ListKind::Compose,
                    head: Box::new(TokenTree::Dollarydoo),
                    tail: Box::new(TokenTree::List {
                        kind: ListKind::Compose,
                        head: Box::new(TokenTree::Anything),
                        tail: Box::new(TokenTree::Nil),
                    }),
                },
            ],
        );
        env.add_type(
            "Mem",
            vec![TokenTree::Fun {
                name: String::from("memOffset"),
                args: vec![TokenTree::Anything],
            }],
        );

        // These are not used in the semantics
        env.add_type("Sreg", vec![]); // Self::make_tt_strings(&[ "%es", "%cs", "%ss", "%ds", "%fs", "%gs" ])
        env.add_type("St", vec![]); // Self::make_tt_strings(&[ "%st", "%st(0)", "%st(1)", "%st(2)", "%st(3)", "%st(4)", "%st(5)", "%st(6)", "%st(7)" ])
        env.add_type("Mm", vec![]); // Self::make_tt_strings(&[ "%mmx0", "%mmx1", "%mmx2", "%mmx3", "%mmx4", "%mmx5", "%mmx6", "%mmx7" ])

        // We don't support labels, so we must make sure these execinstrs never match.
        env.add_type("X86Id", vec![]);

        let mut tt_ops = TokenTree::Nil;
        for op in operands.iter().rev() {
            tt_ops = TokenTree::List {
                kind: ListKind::Comma,
                head: Box::new(op.clone()),
                tail: Box::new(tt_ops),
            };
        }

        let state = CellState {
            tokens: TokenTree::List {
                kind: ListKind::Trace,
                head: Box::new(TokenTree::Fun {
                    name: String::from("execinstr"),
                    args: vec![op.clone(), tt_ops],
                }),
                tail: Box::new(TokenTree::Nil),
            },
        };
        let var_sets = [
            (
                [
                    "RAX",
                    "RBX",
                    "RCX",
                    "RDX",
                    "RSI",
                    "RDI",
                    "RSP",
                    "RBP",
                    "R8",
                    "R9",
                    "R10",
                    "R11",
                    "R12",
                    "R13",
                    "R14",
                    "R15",
                    "RIP",
                    "%virt:R64:0",
                    "%virt:R64:1",
                    "%virt:R64:2",
                ]
                .as_slice(),
                64,
            ),
            (["ZF", "CF", "SF", "AF", "PF", "OF", "DF"].as_slice(), 1),
            (
                [
                    "YMM0",
                    "YMM1",
                    "YMM2",
                    "YMM3",
                    "YMM4",
                    "YMM5",
                    "YMM6",
                    "YMM7",
                    "YMM8",
                    "YMM9",
                    "YMM10",
                    "YMM11",
                    "YMM12",
                    "YMM13",
                    "YMM14",
                    "YMM15",
                    "%virt:Ymm:0",
                    "%virt:Ymm:1",
                    "%virt:Ymm:2",
                    "%virt:Ymm:3",
                ]
                .as_slice(),
                256,
            ),
        ];
        let mut regstate = TokenTree::Nil;
        for (vars, size) in var_sets {
            for var in vars {
                regstate = TokenTree::List {
                    kind: ListKind::Comma,
                    head: Box::new(
                        env.convert_expr(&Expr::parse(&format!("\"{var}\" |-> z3_bitvec(\"{var}\", {size})")).unwrap()),
                    ),
                    tail: Box::new(regstate),
                };
            }
        }

        let mut env = env.with_cell(String::from("k"), state).with_cell(
            String::from("regstate"),
            CellState {
                tokens: regstate,
            },
        );

        env.add_declarations(declarations);
        lazy_static! {
            static ref PRELUDE: Vec<Declaration> = match parse(include_str!("prelude.k")) {
                Ok(v) => v,
                Err(e) => panic!("{e}"),
            };
        }

        env.add_declarations(&PRELUDE);

        let results = env.eval();
        for state in results.iter() {
            let cell = env.get_state_cell(state, "k").unwrap();
            info!("Result: {cell:?}");
            if cell != &TokenTree::Nil {
                error!("\nResult is not nil: {cell:?}");
                return None
            }
        }

        let results = results
            .iter()
            .map(|state| {
                let constraints = state.path_constraints().iter().map(Self::z3_from_tt).collect::<Vec<_>>();
                let result = env.get_state_cell(state, "regstate").unwrap();
                (constraints, Self::build_z3(result))
            })
            .collect::<Vec<_>>();

        if results.len() == 1 && results[0].0.is_empty() {
            let mut results = results;
            Some(results.remove(0).1)
        } else {
            let mut result = HashMap::new();

            for (path, kz3) in results {
                for (loc, expr) in kz3.map {
                    let other_val = result.remove(&loc).unwrap_or_else(|| {
                        Z3Node::OriginalValue(Box::new(match &loc {
                            StorageLocation::Reg(reg) => Z3Node::Var(format!("reg_{reg}")),
                            StorageLocation::Mem {
                                offset,
                                size,
                            } => Z3Node::Memory {
                                computation: Box::new(offset.clone()),
                                size: *size as u32,
                            },
                        }))
                    });
                    let condition = path
                        .iter()
                        .cloned()
                        .reduce(|a, b| Z3Node::Fun {
                            name: Z3Fun::And,
                            args: vec![a, b],
                        })
                        .unwrap();
                    let val = Z3Node::Fun {
                        name: Z3Fun::Ite,
                        args: vec![condition, expr, other_val],
                    };

                    result.insert(loc, val);
                }
            }

            Some(Kz3 {
                map: result.into_iter().collect::<Vec<_>>(),
            })
        }
    }

    fn build_z3(original_tt: &TokenTree) -> Kz3 {
        let mut tt = original_tt;
        debug!("Generating z3 from {tt:?}");
        let mut map = Vec::new();
        let mut done = false;
        while !done && tt != &TokenTree::Nil {
            debug!("Processing {tt:?}");
            let head: &TokenTree = if let TokenTree::List {
                head,
                tail,
                ..
            } = tt
            {
                tt = &**tail;
                head
            } else {
                done = true;
                tt
            };
            let TokenTree::MapTo {
                from,
                to,
            } = head
            else {
                panic!("Expected a map-to in output: {head:?} from {original_tt:?}")
            };
            let loc = match &**from {
                TokenTree::String(storage_loc_name) => StorageLocation::Reg(storage_loc_name.clone()),
                TokenTree::Fun {
                    name,
                    args,
                } if name == "z3_mem" => {
                    let TokenTree::Num(size) = &args[1] else {
                        panic!("z3_mem needs a number as second argument")
                    };

                    StorageLocation::Mem {
                        offset: Self::z3_from_tt(&args[0]),
                        size: *size as usize,
                    }
                },
                _ => panic!("Unable to handle mapping: {from:?} |-> {to:?}"),
            };

            let result = Self::z3_from_tt(to);
            if !result.is_identity(&loc) {
                map.push((loc, result));
            }
        }

        map.reverse();

        Kz3 {
            map,
        }
    }

    fn z3_from_tt(to: &TokenTree) -> Z3Node {
        fn f<const N: usize>(name: Z3Fun, args: [Z3Node; N]) -> Z3Node {
            Z3Node::Fun {
                name,
                args: args.to_vec(),
            }
        }

        fn c(c: impl Into<i128>) -> Z3Node {
            Z3Node::IntConst(c.into())
        }

        macro_rules! impl_simple_mappings {
            (match ($e:expr, $f:expr, $conv:expr) { $($name:pat, $op:expr => $($arg:tt),*;)* } else $var:ident $default:block) => {
                match $e {
                    $(($name, [ $($arg),* ]) => $f($op, [ $($arg),* ].map($conv)),)*
                    $var => $default,
                }
            }
        }

        trace!("z3 for {to:?}");
        use Z3Fun::*;

        let result = match to {
            TokenTree::Fun {
                name,
                args,
            } => impl_simple_mappings!(match ((name.as_str(), args.as_slice()), f, Self::z3_from_tt) {
                "concatenateMInt", Concat => lhs, rhs;
                "__and_bool", And => lhs, rhs;
                "__add_int", Add => lhs, rhs;
                "__sub_int", Sub => lhs, rhs;
                "__mul_int", Mul => lhs, rhs;
                "__eq_bool", Eq => lhs, rhs;
                "__eq_int", Eq => lhs, rhs;
                "__not_bool" | "notBool", Not => b;
                "eqMInt", Eq => lhs, rhs;
                "sgtMInt", BvSignedGt => lhs, rhs;
                "sltMInt", BvSignedLt => lhs, rhs;
                "ugtMInt", BvUnsignedGt => lhs, rhs;
                "ultMInt", BvUnsignedLt => lhs, rhs;
                "uleMInt", BvUnsignedLe => lhs, rhs;
                "ugeMInt", BvUnsignedGe => lhs, rhs;
                "addMInt", BvAdd => lhs, rhs;
                "subMInt", BvSub => lhs, rhs;
                "mulMInt", BvMul => lhs, rhs;
                "xorMInt", BvXor => lhs, rhs;
                "andMInt", BvAnd => lhs, rhs;
                "popCount", BvPopCount => a;
                "svalueMInt", BvToSignedInt => a;
                "uvalueMInt", BvToUnsignedInt => a;
                "orMInt", BvOr => lhs, rhs;
                "lshrMInt", BvLshr => lhs, rhs;
                "rol", BvRol => lhs, rhs;
                "ror", BvRor => lhs, rhs;
                "shiftLeftMInt", BvShl => lhs, rhs;
                "aShiftRightMInt", BvAshr => lhs, rhs;
                "uremMInt", BvUnsignedRem => lhs, rhs;
                "idiv_quotient_int8", SignedDiv(8) => lhs, rhs;
                "idiv_remainder_int8", SignedRem(8) => lhs, rhs;
                "idiv_quotient_int16", SignedDiv(16) => lhs, rhs;
                "idiv_remainder_int16", SignedRem(16) => lhs, rhs;
                "idiv_quotient_int32", SignedDiv(32) => lhs, rhs;
                "idiv_remainder_int32", SignedRem(32) => lhs, rhs;
                "idiv_quotient_int64", SignedDiv(64) => lhs, rhs;
                "idiv_remainder_int64", SignedRem(64) => lhs, rhs;
                "div_quotient_int8", UnsignedDiv(8) => lhs, rhs;
                "div_remainder_int8", UnsignedRem(8) => lhs, rhs;
                "div_quotient_int16", UnsignedDiv(16) => lhs, rhs;
                "div_remainder_int16", UnsignedRem(16) => lhs, rhs;
                "div_quotient_int32", UnsignedDiv(32) => lhs, rhs;
                "div_remainder_int32", UnsignedRem(32) => lhs, rhs;
                "div_quotient_int64", UnsignedDiv(64) => lhs, rhs;
                "div_remainder_int64", UnsignedRem(64) => lhs, rhs;
                "__or_bool", Or => lhs, rhs;
                "__xor_bool", Xor => lhs, rhs;
                "negMInt", BvNot => val;
                "ite", Ite => cond, then, otherwise;
                "plugInMask", PlugInMask => a, b, c;
                "scanReverse", BvScanReverse => a, b, c;
                "scanForward", BvScanForward => a, b, c;
                "bitwidthMInt", BvBitSize => a;
                "__pdep32", Pdep32 => a, b;
                "__pdep64", Pdep64 => a, b;
                "__pextr32", Pextr32 => a, b;
                "__pextr64", Pextr64 => a, b;
                "cmp_double_pred" | "cmp_single_pred" |
                "vfmadd132_double" | "vfmadd231_double" | "vfmadd213_double" | "vfnmadd132_double" | "vfnmadd231_double" |
                "vfnmadd213_double" | "vfmsub132_double" | "vfmsub231_double" | "vfmsub213_double" | "vfnmsub132_double" |
                "vfnmsub231_double" | "vfnmsub213_double" | "vfmadd132_single" | "vfmadd231_single" | "vfmadd213_single" |
                "vfnmadd132_single" | "vfnmadd231_single" | "vfnmadd213_single" | "vfmsub132_single" | "vfmsub231_single" |
                "vfmsub213_single" | "vfnmsub132_single" | "vfnmsub231_single" | "vfnmsub213_single", FpFunc => a, b, c;
                "comisd" | "comiss" | "add_double" | "sub_double" | "mul_double" | "div_double" | "maxcmp_double" |
                "mincmp_double" | "add_single" | "sub_single" | "mul_single" | "div_single" | "maxcmp_single" | "mincmp_single" |
                "cvt_single_to_int32_rm" | "cvt_single_to_fp16_rm" | "cvt_double_to_int64_rm", FpFunc => a, b;
                "cvt_single_to_double" | "cvt_double_to_single" | "cvt_int64_to_double" | "cvt_int32_to_double" |
                "cvt_int64_to_single" | "cvt_int32_to_single" | "cvt_double_to_int64" | "cvt_double_to_int64_truncate" |
                "cvt_double_to_int32" | "cvt_double_to_int32_truncate" | "cvt_single_to_int64" | "cvt_single_to_int64_truncate" |
                "cvt_single_to_int32" | "cvt_single_to_int32_truncate" | "sqrt_double" | "sqrt_single" |
                "approx_reciprocal_double" | "approx_reciprocal_single" | "approx_reciprocal_sqrt_double" |
                "approx_reciprocal_sqrt_single" | "cvt_half_to_single", FpFunc => a;
            } else other {
                match other {
                    ("__instructionByteLength", []) => Z3Node::InstructionByteLength,
                    ("__sameRegisters", [ TokenTree::String(a), TokenTree::String(b) ]) => Z3Node::Fun {
                        name: Z3Fun::SameRegisters,
                        args: vec![
                            Z3Node::Var(a.clone()),
                            Z3Node::Var(b.clone()),
                        ]
                    },
                    ("extractMInt", [ val, TokenTree::Num(lo), TokenTree::Num(hi) ]) => {
                        f(Extract { hi: *hi as u32, lo: *lo as u32 }, [ Self::z3_from_tt(val) ])
                    },
                    ("extractMInt", [ val, lo, hi ]) => {
                        f(DynamicExtract, [ Self::z3_from_tt(val), Self::z3_from_tt(lo), Self::z3_from_tt(hi) ])
                    },
                    ("signExtend", [ val, TokenTree::Num(size) ]) => {
                        f(SignExtend(*size as u32), [ Self::z3_from_tt(val) ])
                    },
                    ("mi", [ TokenTree::Num(size), TokenTree::Num(val) ]) => Z3Node::BvConst {
                        val: *val,
                        size: *size as u32,
                    },
                    ("mi", [ TokenTree::Num(size), TokenTree::Hex(val) ]) => Z3Node::BvConst {
                        val: *val as i128,
                        size: *size as u32,
                    },
                    ("createUndefMInt", [ TokenTree::Num(size) ]) => Z3Node::MIntUndef((*size).try_into().unwrap()),
                    ("mi", [ TokenTree::Num(size), tt ]) => f(MakeBvWithSize(*size as u32), [ Self::z3_from_tt(tt) ]),
                    ("mi", [ size, tt ]) => f(MakeBvWithDynamicSize, [ Self::z3_from_tt(size), Self::z3_from_tt(tt) ]),
                    ("z3_bitvec", [ TokenTree::String(regname), TokenTree::Num(_) ]) => Z3Node::Var(format!("reg_{regname}")),
                    ("z3_mem", [ offset, TokenTree::Num(size) ]) => Z3Node::Memory {
                        computation: Box::new(Self::z3_from_tt(offset)),
                        size: *size as u32,
                    },
                    ("computePCLMULQDQ1" | "computePCLMULQDQ2" | "polarityImpl" | "findLimitIndexE" | "findLimitIndexI" | "equalOrderedImpl" | "expandMask", _) => {
                        Z3Node::Unsupported
                    }
                    (name, args) => panic!("Unknown function: {name}({args:?})"),
                }
            }),
            TokenTree::Typed {
                expr, ..
            } => Self::z3_from_tt(expr),
            TokenTree::Num(n) => c(*n),
            TokenTree::Hex(_) => todo!(),
            TokenTree::String(s) => match s.as_str() {
                "false" => Z3Node::BoolConst(false),
                "true" => Z3Node::BoolConst(true),
                "undefBool" => Z3Node::BoolUndef,
                "undefMInt" => Z3Node::MIntUndef(1),
                "undefMInt8" => Z3Node::MIntUndef(8),
                "undefMInt16" => Z3Node::MIntUndef(16),
                "undefMInt32" => Z3Node::MIntUndef(32),
                "undefMInt64" => Z3Node::MIntUndef(64),
                "%virt:Imm:0" => Z3Node::Imm(0),
                "%virt:Imm:1" => Z3Node::Imm(1),
                "%virt:Imm:2" => Z3Node::Imm(2),
                "%virt:MemOffset:0" => Z3Node::Var(String::from("addr0")),
                "%virt:MemOffset:1" => Z3Node::Var(String::from("addr1")),
                "%virt:MemOffset:2" => Z3Node::Var(String::from("addr2")),
                _ => unimplemented!("conversion from {s:?} to z3"),
            },
            TokenTree::List {
                kind: ListKind::Compose,
                head,
                tail,
            } => match (&**head, &**tail) {
                (TokenTree::Dollarydoo, TokenTree::Hex(h)) => Z3Node::IntConst(*h as i128),
                (TokenTree::Dollarydoo, TokenTree::String(s)) => match s.as_str() {
                    "%virt:Imm:0" => Z3Node::Imm(0),
                    "%virt:Imm:1" => Z3Node::Imm(1),
                    "%virt:Imm:2" => Z3Node::Imm(2),
                    _ => unimplemented!("conversion from {s:?} to z3"),
                },
                other => unimplemented!("conversion from {other:?} to z3"),
            },
            other => unimplemented!("conversion from {other:?} to z3"),
        };

        trace!("z3 for {to:?} = {result:?}");
        result
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use super::Kz3;
    use crate::ast::parse;
    use crate::rewrite::{ListKind, TokenTree};
    use crate::z3::StorageLocation;

    fn f<const N: usize>(name: impl Into<String>, args: [TokenTree; N]) -> TokenTree {
        TokenTree::Fun {
            name: name.into(),
            args: args.to_vec(),
        }
    }

    #[test]
    pub fn build_mov_r16_r16() {
        let declarations = parse(r#"// Autogenerated using stratification.
        requires "x86-configuration.k"
        
        module MOVW-R16-R16
          imports X86-CONFIGURATION
        
          rule <k>
            execinstr (movw R1:R16, R2:R16,  .Operands) => .
          ...</k>
            <regstate>
        RSMap:Map => updateMap(RSMap,
        convToRegKeys(R2) |-> concatenateMInt( extractMInt( getParentValue(R2, RSMap), 0, 48), extractMInt( getParentValue(R1, RSMap), 48, 64))
        )
        
            </regstate>
            
        endmodule
        
        module MOVW-R16-R16-SEMANTICS
          imports MOVW-R16-R16
        endmodule
        "#).unwrap();
        let _kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from("movw")),
            &[TokenTree::String(String::from("%ax")), TokenTree::String(String::from("%di"))],
        )
        .unwrap();
    }

    #[test]
    pub fn build_movl_r32_m32() {
        let declarations = parse(r#"// Autogenerated using stratification.
        requires "x86-configuration.k"

        module MOVL-R32-M32
        imports X86-CONFIGURATION

        context execinstr(movl:Opcode HOLE:Mem, R2:R32,  .Operands) [result(MemOffset)]
        
        rule <k>
            execinstr (movl:Opcode memOffset( MemOff:MInt):MemOffset, R2:R32,  .Operands) =>
            loadFromMemory( MemOff, 32) ~>
            execinstr (movl memOffset( MemOff), R2,  .Operands)
        ...</k>
            <regstate> RSMap:Map </regstate>
                
        rule <k>
            memLoadValue(Mem32:MInt):MemLoadValue ~> execinstr (movl:Opcode memOffset( MemOff:MInt):MemOffset, R2:R32,  .Operands) =>
            .
        ...</k>
            <regstate>
            RSMap:Map => updateMap(RSMap,
        convToRegKeys(R2) |-> concatenateMInt( mi(32, 0), Mem32)
            )
            </regstate>
        endmodule
        "#).unwrap();
        // from: execinstr(var0, Comma(memOffset(var2), (var1):Ty(["%eax", "%ebx", "%ecx", "%edx", "%esi", "%edi", "%esp", "%ebp", "%r8d", "%r9d", "%r10d", "%r11d", "%r12d", "%r13d", "%r14d", "%r15d"]))),

        let _kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from("movl")),
            &[
                TokenTree::Fun {
                    name: String::from("memOffset"),
                    args: vec![TokenTree::String(String::from("%virt:MemOffset:0"))],
                },
                TokenTree::String(String::from("%eax")),
            ],
        )
        .unwrap();
    }

    #[test]
    pub fn check_imm_type_resolution() {
        let declarations = parse(
            r#"// Autogenerated using stratification.
        requires "x86-configuration.k"
        
        module ADCB-RH-RH
          imports X86-CONFIGURATION
        
            rule <k> execinstr (adcb I:Imm, R2:Rh,  .Operands) => BOOM()</k>
        
            rule <k> execinstr (adcb I:Rh, R2:Rh,  .Operands) => .</k>
            
        endmodule
        
        module ADCB-RH-RH-SEMANTICS
          imports ADCB-RH-RH
        endmodule
        "#,
        )
        .unwrap();
        let _kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from("adcb")),
            &[TokenTree::String(String::from("%ah")), TokenTree::String(String::from("%bh"))],
        )
        .unwrap();
    }

    #[test]
    pub fn test_adcq_r64_imm8() {
        let declarations = parse(r#"// Autogenerated using stratification.
        requires "x86-configuration.k"
        
        module ADCQ-R64-IMM8
          imports X86-CONFIGURATION
        
          rule <k>
            execinstr (adcq Imm8:Imm, R2:R64,  .Operands) => .
          ...</k>
            <regstate>
        RSMap:Map => updateMap(RSMap,
        convToRegKeys(R2) |-> extractMInt( addMInt( (#ifMInt eqMInt(getFlag("CF", RSMap), mi(1,1)) #then addMInt( concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))), mi(65, 1)) #else concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))) #fi), concatenateMInt( mi(1, 0), getParentValue(R2, RSMap))), 1, 65)
        
        "CF" |-> extractMInt( addMInt( (#ifMInt eqMInt(getFlag("CF", RSMap), mi(1,1)) #then addMInt( concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))), mi(65, 1)) #else concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))) #fi), concatenateMInt( mi(1, 0), getParentValue(R2, RSMap))), 0, 1)
        
        "PF" |-> (#ifMInt (notBool (((((((eqMInt( extractMInt( addMInt( (#ifMInt eqMInt(getFlag("CF", RSMap), mi(1,1)) #then addMInt( concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))), mi(65, 1)) #else concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))) #fi), concatenateMInt( mi(1, 0), getParentValue(R2, RSMap))), 64, 65), mi(1, 1)) xorBool eqMInt( extractMInt( addMInt( (#ifMInt eqMInt(getFlag("CF", RSMap), mi(1,1)) #then addMInt( concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))), mi(65, 1)) #else concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))) #fi), concatenateMInt( mi(1, 0), getParentValue(R2, RSMap))), 63, 64), mi(1, 1))) xorBool eqMInt( extractMInt( addMInt( (#ifMInt eqMInt(getFlag("CF", RSMap), mi(1,1)) #then addMInt( concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))), mi(65, 1)) #else concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))) #fi), concatenateMInt( mi(1, 0), getParentValue(R2, RSMap))), 62, 63), mi(1, 1))) xorBool eqMInt( extractMInt( addMInt( (#ifMInt eqMInt(getFlag("CF", RSMap), mi(1,1)) #then addMInt( concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))), mi(65, 1)) #else concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))) #fi), concatenateMInt( mi(1, 0), getParentValue(R2, RSMap))), 61, 62), mi(1, 1))) xorBool eqMInt( extractMInt( addMInt( (#ifMInt eqMInt(getFlag("CF", RSMap), mi(1,1)) #then addMInt( concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))), mi(65, 1)) #else concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))) #fi), concatenateMInt( mi(1, 0), getParentValue(R2, RSMap))), 60, 61), mi(1, 1))) xorBool eqMInt( extractMInt( addMInt( (#ifMInt eqMInt(getFlag("CF", RSMap), mi(1,1)) #then addMInt( concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))), mi(65, 1)) #else concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))) #fi), concatenateMInt( mi(1, 0), getParentValue(R2, RSMap))), 59, 60), mi(1, 1))) xorBool eqMInt( extractMInt( addMInt( (#ifMInt eqMInt(getFlag("CF", RSMap), mi(1,1)) #then addMInt( concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))), mi(65, 1)) #else concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))) #fi), concatenateMInt( mi(1, 0), getParentValue(R2, RSMap))), 58, 59), mi(1, 1))) xorBool eqMInt( extractMInt( addMInt( (#ifMInt eqMInt(getFlag("CF", RSMap), mi(1,1)) #then addMInt( concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))), mi(65, 1)) #else concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))) #fi), concatenateMInt( mi(1, 0), getParentValue(R2, RSMap))), 57, 58), mi(1, 1)))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "AF" |-> xorMInt( xorMInt( extractMInt( handleImmediateWithSignExtend(Imm8, 8, 8), 3, 4), extractMInt( getParentValue(R2, RSMap), 59, 60)), extractMInt( addMInt( (#ifMInt eqMInt(getFlag("CF", RSMap), mi(1,1)) #then addMInt( concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))), mi(65, 1)) #else concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))) #fi), concatenateMInt( mi(1, 0), getParentValue(R2, RSMap))), 60, 61))
        
        "ZF" |-> (#ifMInt eqMInt( extractMInt( addMInt( (#ifMInt eqMInt(getFlag("CF", RSMap), mi(1,1)) #then addMInt( concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))), mi(65, 1)) #else concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))) #fi), concatenateMInt( mi(1, 0), getParentValue(R2, RSMap))), 1, 65), mi(64, 0)) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "SF" |-> extractMInt( addMInt( (#ifMInt eqMInt(getFlag("CF", RSMap), mi(1,1)) #then addMInt( concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))), mi(65, 1)) #else concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))) #fi), concatenateMInt( mi(1, 0), getParentValue(R2, RSMap))), 1, 2)
        
        "OF" |-> (#ifMInt ((eqMInt( extractMInt( mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8))), 0, 1), mi(1, 1)) ==Bool eqMInt( extractMInt( getParentValue(R2, RSMap), 0, 1), mi(1, 1))) andBool (notBool (eqMInt( extractMInt( mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8))), 0, 1), mi(1, 1)) ==Bool eqMInt( extractMInt( addMInt( (#ifMInt eqMInt(getFlag("CF", RSMap), mi(1,1)) #then addMInt( concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))), mi(65, 1)) #else concatenateMInt( mi(1, 0), mi(64, svalueMInt(handleImmediateWithSignExtend(Imm8, 8, 8)))) #fi), concatenateMInt( mi(1, 0), getParentValue(R2, RSMap))), 1, 2), mi(1, 1))))) #then mi(1, 1) #else mi(1, 0) #fi)
        )
        
            </regstate>
            
        endmodule
        
        module ADCQ-R64-IMM8-SEMANTICS
          imports ADCQ-R64-IMM8
        endmodule
        "#).unwrap();
        let _kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from("adcq")),
            &[
                TokenTree::List {
                    kind: ListKind::Compose,
                    head: Box::new(TokenTree::Dollarydoo),
                    tail: Box::new(TokenTree::Hex(0x13)),
                },
                TokenTree::String(String::from("%rax")),
            ],
        )
        .unwrap();
    }

    #[test]
    pub fn build_sarl_r32_cl() {
        let declarations = parse(r#"// Autogenerated using stratification.
        requires "x86-configuration.k"
        
        module SARL-R32-CL
          imports X86-CONFIGURATION
        
          rule <k>
            execinstr (sarl %cl, R2:R32,  .Operands) => .
          ...</k>
            <regstate>
        RSMap:Map => updateMap(RSMap,
        convToRegKeys(R2) |-> concatenateMInt( mi(32, 0), extractMInt( aShiftRightMInt( concatenateMInt( extractMInt( getParentValue(R2, RSMap), 32, 64), mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 0, 32))
        
        "CF" |-> (#ifMInt (((notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0))) andBool eqMInt( extractMInt( aShiftRightMInt( concatenateMInt( extractMInt( getParentValue(R2, RSMap), 32, 64), mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 32, 33), mi(1, 1))) orBool ((notBool (notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("CF", RSMap), mi(1,1)))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "PF" |-> (#ifMInt (((notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0))) andBool (notBool (((((((eqMInt( extractMInt( aShiftRightMInt( concatenateMInt( extractMInt( getParentValue(R2, RSMap), 32, 64), mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 31, 32), mi(1, 1)) xorBool eqMInt( extractMInt( aShiftRightMInt( concatenateMInt( extractMInt( getParentValue(R2, RSMap), 32, 64), mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 30, 31), mi(1, 1))) xorBool eqMInt( extractMInt( aShiftRightMInt( concatenateMInt( extractMInt( getParentValue(R2, RSMap), 32, 64), mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 29, 30), mi(1, 1))) xorBool eqMInt( extractMInt( aShiftRightMInt( concatenateMInt( extractMInt( getParentValue(R2, RSMap), 32, 64), mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 28, 29), mi(1, 1))) xorBool eqMInt( extractMInt( aShiftRightMInt( concatenateMInt( extractMInt( getParentValue(R2, RSMap), 32, 64), mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 27, 28), mi(1, 1))) xorBool eqMInt( extractMInt( aShiftRightMInt( concatenateMInt( extractMInt( getParentValue(R2, RSMap), 32, 64), mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 26, 27), mi(1, 1))) xorBool eqMInt( extractMInt( aShiftRightMInt( concatenateMInt( extractMInt( getParentValue(R2, RSMap), 32, 64), mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 25, 26), mi(1, 1))) xorBool eqMInt( extractMInt( aShiftRightMInt( concatenateMInt( extractMInt( getParentValue(R2, RSMap), 32, 64), mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 24, 25), mi(1, 1))))) orBool ((notBool (notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("PF", RSMap), mi(1,1)))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "AF" |-> (#ifMInt (((notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0))) andBool (undefBool)) orBool ((notBool (notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("AF", RSMap), mi(1,1)))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "ZF" |-> (#ifMInt (((notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0))) andBool eqMInt( extractMInt( aShiftRightMInt( concatenateMInt( extractMInt( getParentValue(R2, RSMap), 32, 64), mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 0, 32), mi(32, 0))) orBool ((notBool (notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("ZF", RSMap), mi(1,1)))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "SF" |-> (#ifMInt (((notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0))) andBool eqMInt( extractMInt( aShiftRightMInt( concatenateMInt( extractMInt( getParentValue(R2, RSMap), 32, 64), mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 0, 1), mi(1, 1))) orBool ((notBool (notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("SF", RSMap), mi(1,1)))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "OF" |-> (#ifMInt ((eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 1)) andBool false) orBool ((notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 1))) andBool (((notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0))) andBool (undefBool)) orBool ((notBool (notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("OF", RSMap), mi(1,1)))))) #then mi(1, 1) #else mi(1, 0) #fi)
        )
        
            </regstate>
            
        endmodule
        
        module SARL-R32-CL-SEMANTICS
          imports SARL-R32-CL
        endmodule
        "#).unwrap();
        let _kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from("sarl")),
            &[
                TokenTree::String(String::from("%cl")),
                TokenTree::String(String::from("%eax")),
            ],
        )
        .unwrap();
    }

    #[test]
    pub fn build_shrb_m8_imm8() {
        let declarations = parse(r#"// Autogenerated using stratification.
        requires "x86-configuration.k"
        
        module SHRB-M8-IMM8
          imports X86-CONFIGURATION
        
          context execinstr(shrb:Opcode Imm8:Imm, HOLE:Mem,  .Operands) [result(MemOffset)]
          
          rule <k>
            execinstr (shrb:Opcode Imm8:Imm, memOffset( MemOff:MInt):MemOffset,  .Operands) =>
              loadFromMemory( MemOff, 8) ~>
              execinstr (shrb Imm8, memOffset( MemOff),  .Operands)
          ...</k>
            <regstate> RSMap:Map </regstate>
                  
          rule <k>
            memLoadValue(Mem8:MInt):MemLoadValue ~> execinstr (shrb:Opcode Imm8:Imm, memOffset( MemOff:MInt):MemOffset,  .Operands) =>
              
                    storeToMemory(
                      extractMInt( lshrMInt( concatenateMInt( Mem8, mi(1, 0)), uvalueMInt(concatenateMInt( mi(1, 0), andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31))))), 0, 8),
                      MemOff,
                      8
                    )
                  
          ...</k>
            <regstate>
              RSMap:Map => updateMap(RSMap,
        "CF" |-> (#ifMInt ((ugeMInt( andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31)), mi(8, 8)) andBool (undefBool)) orBool ((notBool ugeMInt( andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31)), mi(8, 8))) andBool (((notBool eqMInt( andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31)), mi(8, 0))) andBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem8, mi(1, 0)), uvalueMInt(concatenateMInt( mi(1, 0), andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31))))), 8, 9), mi(1, 1))) orBool ((notBool (notBool eqMInt( andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("CF", RSMap), mi(1,1)))))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "PF" |-> (#ifMInt (((notBool eqMInt( andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31)), mi(8, 0))) andBool (notBool (((((((eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem8, mi(1, 0)), uvalueMInt(concatenateMInt( mi(1, 0), andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31))))), 7, 8), mi(1, 1)) xorBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem8, mi(1, 0)), uvalueMInt(concatenateMInt( mi(1, 0), andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31))))), 6, 7), mi(1, 1))) xorBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem8, mi(1, 0)), uvalueMInt(concatenateMInt( mi(1, 0), andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31))))), 5, 6), mi(1, 1))) xorBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem8, mi(1, 0)), uvalueMInt(concatenateMInt( mi(1, 0), andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31))))), 4, 5), mi(1, 1))) xorBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem8, mi(1, 0)), uvalueMInt(concatenateMInt( mi(1, 0), andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31))))), 3, 4), mi(1, 1))) xorBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem8, mi(1, 0)), uvalueMInt(concatenateMInt( mi(1, 0), andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31))))), 2, 3), mi(1, 1))) xorBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem8, mi(1, 0)), uvalueMInt(concatenateMInt( mi(1, 0), andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31))))), 1, 2), mi(1, 1))) xorBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem8, mi(1, 0)), uvalueMInt(concatenateMInt( mi(1, 0), andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31))))), 0, 1), mi(1, 1))))) orBool ((notBool (notBool eqMInt( andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("PF", RSMap), mi(1,1)))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "AF" |-> (#ifMInt (((notBool eqMInt( andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31)), mi(8, 0))) andBool (undefBool)) orBool ((notBool (notBool eqMInt( andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("AF", RSMap), mi(1,1)))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "ZF" |-> (#ifMInt (((notBool eqMInt( andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31)), mi(8, 0))) andBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem8, mi(1, 0)), uvalueMInt(concatenateMInt( mi(1, 0), andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31))))), 0, 8), mi(8, 0))) orBool ((notBool (notBool eqMInt( andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("ZF", RSMap), mi(1,1)))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "SF" |-> (#ifMInt (((notBool eqMInt( andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31)), mi(8, 0))) andBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem8, mi(1, 0)), uvalueMInt(concatenateMInt( mi(1, 0), andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31))))), 0, 1), mi(1, 1))) orBool ((notBool (notBool eqMInt( andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("SF", RSMap), mi(1,1)))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "OF" |-> (#ifMInt ((eqMInt( andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31)), mi(8, 1)) andBool eqMInt( extractMInt( Mem8, 0, 1), mi(1, 1))) orBool ((notBool eqMInt( andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31)), mi(8, 1))) andBool (((notBool eqMInt( andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31)), mi(8, 0))) andBool (undefBool)) orBool ((notBool (notBool eqMInt( andMInt( handleImmediateWithSignExtend(Imm8, 8, 8), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("OF", RSMap), mi(1,1)))))) #then mi(1, 1) #else mi(1, 0) #fi)
              )
            </regstate>
        endmodule
        "#).unwrap();
        let _kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from("shrb")),
            &[
                TokenTree::List {
                    kind: ListKind::Compose,
                    head: Box::new(TokenTree::Dollarydoo),
                    tail: Box::new(TokenTree::Hex(5)),
                },
                TokenTree::Fun {
                    name: String::from("memOffset"),
                    args: vec![TokenTree::Num(0x1234)],
                },
            ],
        )
        .unwrap();
    }

    #[test]
    pub fn build_shrl_m32_cl() {
        let declarations = parse(r#"// Autogenerated using stratification.
        requires "x86-configuration.k"
        
        module SHRL-M32-CL
          imports X86-CONFIGURATION

          rule <k>
            execinstr (shrl  M:Mem,  .Operands) =>  execinstr (shrl $0x1, M,  .Operands)
          ...</k>        
        
          context execinstr(shrl:Opcode %cl, HOLE:Mem,  .Operands) [result(MemOffset)]
          
          rule <k>
            execinstr (shrl:Opcode %cl, memOffset( MemOff:MInt):MemOffset,  .Operands) =>
              loadFromMemory( MemOff, 32) ~>
              execinstr (shrl %cl, memOffset( MemOff),  .Operands)
          ...</k>
            <regstate> RSMap:Map </regstate>
                  
          rule <k>
            memLoadValue(Mem32:MInt):MemLoadValue ~> execinstr (shrl:Opcode %cl, memOffset( MemOff:MInt):MemOffset,  .Operands) =>
              
                    storeToMemory(
                      extractMInt( lshrMInt( concatenateMInt( Mem32, mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 0, 32),
                      MemOff,
                      32
                    )
                  
          ...</k>
            <regstate>
              RSMap:Map => updateMap(RSMap,
        "CF" |-> (#ifMInt ((ugeMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 32)) andBool (undefBool)) orBool ((notBool ugeMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 32))) andBool (((notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0))) andBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem32, mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 32, 33), mi(1, 1))) orBool ((notBool (notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("CF", RSMap), mi(1,1)))))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "PF" |-> (#ifMInt (((notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0))) andBool (notBool (((((((eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem32, mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 31, 32), mi(1, 1)) xorBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem32, mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 30, 31), mi(1, 1))) xorBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem32, mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 29, 30), mi(1, 1))) xorBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem32, mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 28, 29), mi(1, 1))) xorBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem32, mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 27, 28), mi(1, 1))) xorBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem32, mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 26, 27), mi(1, 1))) xorBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem32, mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 25, 26), mi(1, 1))) xorBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem32, mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 24, 25), mi(1, 1))))) orBool ((notBool (notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("PF", RSMap), mi(1,1)))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "AF" |-> (#ifMInt (((notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0))) andBool (undefBool)) orBool ((notBool (notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("AF", RSMap), mi(1,1)))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "ZF" |-> (#ifMInt (((notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0))) andBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem32, mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 0, 32), mi(32, 0))) orBool ((notBool (notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("ZF", RSMap), mi(1,1)))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "SF" |-> (#ifMInt (((notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0))) andBool eqMInt( extractMInt( lshrMInt( concatenateMInt( Mem32, mi(1, 0)), uvalueMInt(concatenateMInt( mi(25, 0), andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31))))), 0, 1), mi(1, 1))) orBool ((notBool (notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("SF", RSMap), mi(1,1)))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "OF" |-> (#ifMInt ((eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 1)) andBool eqMInt( extractMInt( Mem32, 0, 1), mi(1, 1))) orBool ((notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 1))) andBool (((notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0))) andBool (undefBool)) orBool ((notBool (notBool eqMInt( andMInt( extractMInt( getParentValue(%rcx, RSMap), 56, 64), mi(8, 31)), mi(8, 0)))) andBool eqMInt(getFlag("OF", RSMap), mi(1,1)))))) #then mi(1, 1) #else mi(1, 0) #fi)
              )
            </regstate>
        endmodule
        "#).unwrap();
        let _kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from("shrl")),
            &[
                TokenTree::String(String::from("%cl")),
                TokenTree::Fun {
                    name: String::from("memOffset"),
                    args: vec![TokenTree::Num(0x1234)],
                },
            ],
        )
        .unwrap();
    }

    #[test]
    pub fn build_vpshufd_xmm_m128_imm8() {
        let declarations = parse(r#"// Autogenerated using stratification.
        requires "x86-configuration.k"
        
        module VPSHUFD-XMM-M128-IMM8
          imports X86-CONFIGURATION
        
          context execinstr(vpshufd:Opcode Imm8:Imm, HOLE:Mem, R3:Xmm,  .Operands) [result(MemOffset)]
          
          rule <k>
            execinstr (vpshufd:Opcode Imm8:Imm, memOffset( MemOff:MInt):MemOffset, R3:Xmm,  .Operands) =>
              loadFromMemory( MemOff, 128) ~>
              execinstr (vpshufd Imm8, memOffset( MemOff), R3:Xmm,  .Operands)
          ...</k>
            <regstate> RSMap:Map </regstate>
                  
          rule <k>
            memLoadValue(Mem128:MInt):MemLoadValue ~> execinstr (vpshufd:Opcode Imm8:Imm, memOffset( MemOff:MInt):MemOffset, R3:Xmm,  .Operands) =>
              .
          ...</k>
            <regstate>
              RSMap:Map => updateMap(RSMap,
        convToRegKeys(R3) |-> concatenateMInt( mi(128, 0), concatenateMInt( extractMInt( lshrMInt( Mem128, uvalueMInt(shiftLeftMInt( concatenateMInt( mi(126, 0), extractMInt( handleImmediateWithSignExtend(Imm8, 8, 8), 0, 2)), uvalueMInt(mi(128, 5))))), 96, 128), concatenateMInt( extractMInt( lshrMInt( Mem128, uvalueMInt(shiftLeftMInt( concatenateMInt( mi(126, 0), extractMInt( handleImmediateWithSignExtend(Imm8, 8, 8), 2, 4)), uvalueMInt(mi(128, 5))))), 96, 128), concatenateMInt( extractMInt( lshrMInt( Mem128, uvalueMInt(shiftLeftMInt( concatenateMInt( mi(126, 0), extractMInt( handleImmediateWithSignExtend(Imm8, 8, 8), 4, 6)), uvalueMInt(mi(128, 5))))), 96, 128), extractMInt( lshrMInt( Mem128, uvalueMInt(shiftLeftMInt( concatenateMInt( mi(126, 0), extractMInt( handleImmediateWithSignExtend(Imm8, 8, 8), 6, 8)), uvalueMInt(mi(128, 5))))), 96, 128)))))
              )
            </regstate>
        endmodule
        "#).unwrap();
        let _kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from("vpshufd")),
            &[
                TokenTree::List {
                    kind: ListKind::Compose,
                    head: Box::new(TokenTree::Dollarydoo),
                    tail: Box::new(TokenTree::Hex(5)),
                },
                TokenTree::Fun {
                    name: String::from("memOffset"),
                    args: vec![TokenTree::Num(0x1234)],
                },
                TokenTree::String(String::from("%xmm9")),
            ],
        )
        .unwrap();
    }

    #[test]
    pub fn build_xaddl_m32_r32() {
        let declarations = parse(r#"// Autogenerated using stratification.
        requires "x86-configuration.k"
        
        module XADDL-M32-R32
          imports X86-CONFIGURATION
        
          context execinstr(xaddl:Opcode R1:R32, HOLE:Mem,  .Operands) [result(MemOffset)]
          
          rule <k>
            execinstr (xaddl:Opcode R1:R32, memOffset( MemOff:MInt):MemOffset,  .Operands) =>
              loadFromMemory( MemOff, 32) ~>
              execinstr (xaddl R1, memOffset( MemOff),  .Operands)
          ...</k>
            <regstate> RSMap:Map </regstate>
                  
          rule <k>
            memLoadValue(Mem32:MInt):MemLoadValue ~> execinstr (xaddl:Opcode R1:R32, memOffset( MemOff:MInt):MemOffset,  .Operands) =>
              
                    storeToMemory(
                      extractMInt( addMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R1, RSMap), 32, 64)), concatenateMInt( mi(1, 0), Mem32)), 1, 33),
                      MemOff,
                      32
                    )
                  
          ...</k>
            <regstate>
              RSMap:Map => updateMap(RSMap,
        convToRegKeys(R1) |-> concatenateMInt( mi(32, 0), Mem32)
        
        "CF" |-> extractMInt( addMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R1, RSMap), 32, 64)), concatenateMInt( mi(1, 0), Mem32)), 0, 1)
        
        "PF" |-> (#ifMInt (notBool (((((((eqMInt( extractMInt( addMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R1, RSMap), 32, 64)), concatenateMInt( mi(1, 0), Mem32)), 32, 33), mi(1, 1)) xorBool eqMInt( extractMInt( addMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R1, RSMap), 32, 64)), concatenateMInt( mi(1, 0), Mem32)), 31, 32), mi(1, 1))) xorBool eqMInt( extractMInt( addMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R1, RSMap), 32, 64)), concatenateMInt( mi(1, 0), Mem32)), 30, 31), mi(1, 1))) xorBool eqMInt( extractMInt( addMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R1, RSMap), 32, 64)), concatenateMInt( mi(1, 0), Mem32)), 29, 30), mi(1, 1))) xorBool eqMInt( extractMInt( addMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R1, RSMap), 32, 64)), concatenateMInt( mi(1, 0), Mem32)), 28, 29), mi(1, 1))) xorBool eqMInt( extractMInt( addMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R1, RSMap), 32, 64)), concatenateMInt( mi(1, 0), Mem32)), 27, 28), mi(1, 1))) xorBool eqMInt( extractMInt( addMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R1, RSMap), 32, 64)), concatenateMInt( mi(1, 0), Mem32)), 26, 27), mi(1, 1))) xorBool eqMInt( extractMInt( addMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R1, RSMap), 32, 64)), concatenateMInt( mi(1, 0), Mem32)), 25, 26), mi(1, 1)))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "AF" |-> xorMInt( xorMInt( extractMInt( getParentValue(R1, RSMap), 59, 60), extractMInt( Mem32, 27, 28)), extractMInt( addMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R1, RSMap), 32, 64)), concatenateMInt( mi(1, 0), Mem32)), 28, 29))
        
        "ZF" |-> (#ifMInt eqMInt( extractMInt( addMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R1, RSMap), 32, 64)), concatenateMInt( mi(1, 0), Mem32)), 1, 33), mi(32, 0)) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "SF" |-> extractMInt( addMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R1, RSMap), 32, 64)), concatenateMInt( mi(1, 0), Mem32)), 1, 2)
        
        "OF" |-> (#ifMInt ((eqMInt( extractMInt( getParentValue(R1, RSMap), 32, 33), mi(1, 1)) ==Bool eqMInt( extractMInt( Mem32, 0, 1), mi(1, 1))) andBool (notBool (eqMInt( extractMInt( getParentValue(R1, RSMap), 32, 33), mi(1, 1)) ==Bool eqMInt( extractMInt( addMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R1, RSMap), 32, 64)), concatenateMInt( mi(1, 0), Mem32)), 1, 2), mi(1, 1))))) #then mi(1, 1) #else mi(1, 0) #fi)
              )
            </regstate>
        endmodule
        "#).unwrap();
        let _kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from("xaddl")),
            &[
                TokenTree::String(String::from("%ecx")),
                f(
                    "memOffset",
                    [f(
                        "addMInt",
                        [
                            f(
                                "mulMInt",
                                [
                                    f("z3_bitvec", [TokenTree::String(String::from("%r9")), TokenTree::Num(64)]),
                                    TokenTree::Num(8),
                                ],
                            ),
                            f(
                                "addMInt",
                                [
                                    f(
                                        "z3_bitvec",
                                        [TokenTree::String(String::from("%rax")), TokenTree::Num(0x1234321)],
                                    ),
                                    TokenTree::Num(1),
                                ],
                            ),
                        ],
                    )],
                ),
            ],
        )
        .unwrap();
    }

    #[test]
    pub fn build_loope_rel8() {
        let declarations = parse(r#"requires "x86-configuration.k"
        module LOOPE-REL8
          imports X86-CONFIGURATION
          imports X86-FLAG-CHECS-SYNTAX
        
          rule <k> 
            execinstr (loope Imm8:Imm, .Operands) => execinstr (loope Imm8, subMInt(getRegisterValue(%rcx, RSMap), mi(64, 1)), .Operands)
          ...</k>
            <regstate> RSMap </regstate>
        
          rule <k> 
            execinstr (loope Imm8:Imm, Count:MInt,  .Operands) => .
          ...</k>
              <regstate> RSMap => updateMap(RSMap, 
                  ("RIP" |-> addMInt({RSMap["RIP"]}:>MInt, handleImmediateWithSignExtend(Imm8, 8, 64)))
                  ("RCX" |-> Count)
                  )
              </regstate>
                requires notBool eqMInt(Count, mi(bitwidthMInt(Count), 0))
                  andBool eqMInt({RSMap["ZF"]}:>MInt, mi(1, 1))
        
          rule <k> 
            execinstr (loope Imm8:Imm, Count:MInt,  .Operands) => .
          ...</k>
              <regstate> RSMap => updateMap(RSMap, 
                  ("RCX" |-> Count)
                  )
              </regstate>
                requires eqMInt(Count, mi(bitwidthMInt(Count), 0))
                  orBool notBool eqMInt({RSMap["ZF"]}:>MInt, mi(1, 1))
        
        endmodule
        requires "x86-configuration.k"


        module LOOPE-LABEL
        imports X86-CONFIGURATION
        imports X86-FLAG-CHECS-SYNTAX

        rule <k> 
            execinstr (loope LabelId:X86Id, .Operands) => execinstr (loope LabelId, subMInt(getRegisterValue(%rcx, RSMap), mi(64, 1)), .Operands)
        ...</k>
            <regstate> RSMap </regstate>

        rule <k> 
            execinstr (loope LabelId:X86Id, Count:MInt,  .Operands) => .
        ...</k>
            <regstate> RSMap => updateMap(RSMap, 
                ("RIP" |-> Target)
                ("RCX" |-> Count)
                )
            </regstate>
            <functargets>... LabelId |-> Target  ...</functargets>
                requires notBool eqMInt(Count, mi(bitwidthMInt(Count), 0))
                andBool eqMInt({RSMap["ZF"]}:>MInt, mi(1, 1))

        rule <k> 
            execinstr (loope LabelId:X86Id, Count:MInt,  .Operands) => .
        ...</k>
            <regstate> RSMap => updateMap(RSMap, 
                ("RCX" |-> Count)
                )
            </regstate>
                requires eqMInt(Count, mi(bitwidthMInt(Count), 0))
                orBool notBool eqMInt({RSMap["ZF"]}:>MInt, mi(1, 1))

        endmodule
        "#).unwrap();
        let _kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from("loope")),
            &[TokenTree::List {
                kind: ListKind::Compose,
                head: Box::new(TokenTree::Dollarydoo),
                tail: Box::new(TokenTree::Hex(5)),
            }],
        )
        .unwrap();
    }

    #[test]
    pub fn build_shrdl_r32_r32_cl() {
        let declarations = parse(
            r#"
        module SHLDL-R32-R32
        imports X86-CONFIGURATION

        rule <k>
            execinstr (shldl %cl, R2:R32, R1:R32,  .Operands) =>  
            execinstr (shldl R1, getRegisterValue(R1, RSMap), getRegisterValue(R2, RSMap), 
                shiftCountMask(getRegisterValue(%cl, RSMap), 32),  .Operands)
        ...</k>
            <regstate> RSMap </regstate>

        rule <k>
            execinstr (shldl R, MIdest:MInt, MIsrc:MInt, MIcount:MInt, .Operands) => 
            setParentValue(concatenateMInt(mi(32,0), MIdest), R) // Intel Bug
        ...</k> 
            requires eqMInt(MIcount, mi(bitwidthMInt(MIcount), 0))

        rule <k>
            execinstr (shldl R, MIdest:MInt, MIsrc:MInt, MIcount:MInt, .Operands) => .
        ...</k> 
        <regstate>
        RSMap:Map => updateMap(RSMap,
        convToRegKeys(R) |-> (undefMInt)
            "ZF" |-> (undefMInt)
            "SF" |-> (undefMInt)
            "CF" |-> (undefMInt)
            "OF" |-> (undefMInt)
            "PF" |-> (undefMInt)
            "AF" |-> (undefMInt)
        )
        </regstate>
            requires ugtMInt(MIcount, mi(bitwidthMInt(MIcount), bitwidthMInt(MIdest)))


        rule <k>
            execinstr (shldl R, MIdest:MInt, MIsrc:MInt, MIcount:MInt, .Operands) => 
            execinstr (shldl R, MIdest:MInt, MIsrc:MInt, MIcount:MInt, 
                orMInt( shiftLeftMInt(MIdest, uvalueMInt(MIcount)),
                lshrMInt(MIsrc, bitwidthMInt(MIdest) -Int uvalueMInt(MIcount))),
                .Operands) 
        ...</k> 
            requires uleMInt(MIcount, mi(bitwidthMInt(MIcount), bitwidthMInt(MIdest)))
            andBool (notBool eqMInt(MIcount, mi(bitwidthMInt(MIcount), 0)))

        rule <k>
            execinstr (shldl R, MIdest:MInt, MIsrc:MInt, MIcount:MInt, MIresult:MInt, .Operands) => 
            setFlag(extractMInt(MIdest, uvalueMInt(MIcount) -Int 1, uvalueMInt(MIcount)), "CF") ~> 
            updateSignFlag(MIresult) ~> 
            updateZeroFlag(MIresult) ~> 
            updateParityFlag(MIresult) ~> 

            setFlag(xorMInt(extractMInt(MIdest, 0, 1), extractMInt(MIresult, 0, 1)), "OF") ~>
            setFlag(undefMInt, "AF") ~> 
            setParentValue(concatenateMInt(mi(32,0), MIresult), R)
        ...</k> 
            requires eqMInt(MIcount, mi(bitwidthMInt(MIcount), 1))
        
        rule <k>
            execinstr (shldl R, MIdest:MInt, MIsrc:MInt, MIcount:MInt, MIresult:MInt, .Operands) => 
            setFlag(extractMInt(MIdest, uvalueMInt(MIcount) -Int 1, uvalueMInt(MIcount)), "CF") ~> 
            updateSignFlag(MIresult) ~> 
            updateZeroFlag(MIresult) ~> 
            updateParityFlag(MIresult) ~> 

            setFlag(undefMInt, "OF") ~>
            setFlag(undefMInt, "AF") ~> 
            setParentValue(concatenateMInt(mi(32,0), MIresult), R)
        ...</k> 
            requires uleMInt(MIcount, mi(bitwidthMInt(MIcount), bitwidthMInt(MIdest)))
                andBool (notBool eqMInt(MIcount, mi(bitwidthMInt(MIcount), 1)))
                andBool (notBool eqMInt(MIcount, mi(bitwidthMInt(MIcount), 0)))
        endmodule// Autogenerated using stratification.
        requires "x86-configuration.k"
        "#,
        )
        .unwrap();
        let kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from(r#"shldl"#)),
            &[
                // shldl %cl, R2:R32, R1:R32
                TokenTree::String(String::from("%cl")),
                TokenTree::String(String::from("%eax")),
                TokenTree::String(String::from("%ebx")),
            ],
        )
        .unwrap();

        println!("{kz3:#?}");
    }

    #[test]
    pub fn build_pclmulqdq_xmm_xmm_imm8() {
        let declarations = parse(
            r#"requires "x86-configuration.k"
        
        module PCLMULQDQ-XMM-XMM-IMM8
          imports X86-CONFIGURATION
        
          rule <k>
            execinstr (pclmulqdq Imm8:Imm, R2:Xmm, R3:Xmm,  .Operands) => 
              execinstr(pclmulqdq 
                  selectSlice(getRegisterValue(R3, RSMap), handleImmediateWithSignExtend(Imm8,
                      8, 8), 7, 64, 0),
                  selectSlice(getRegisterValue(R2, RSMap), handleImmediateWithSignExtend(Imm8,
                      8, 8), 3, 64, 0), R3
                  , .Operands)
          ...</k>
            <regstate> RSMap </regstate>
        
          rule <k>
            execinstr (pclmulqdq TEMP1:MInt, TEMP2:MInt, R3:Xmm,   .Operands) => 
              setRegisterValue(
                  orMInt(
                    computePCLMULQDQ1(TEMP1, TEMP2, mi(128, 0), 0, 63), 
                    computePCLMULQDQ2(TEMP1, TEMP2, mi(128, 0), 64, 126) 
                    ), R3)
          ...</k>
        endmodule
        
        module PCLMULQDQ-XMM-XMM-IMM8-SEMANTICS
          imports PCLMULQDQ-XMM-XMM-IMM8
        endmodule
        "#,
        )
        .unwrap();
        let _kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from(r#"pclmulqdq"#)),
            &[
                TokenTree::List {
                    kind: ListKind::Compose,
                    head: Box::new(TokenTree::Dollarydoo),
                    tail: Box::new(TokenTree::Hex(5)),
                },
                TokenTree::String(String::from("%xmm0")),
                TokenTree::String(String::from("%xmm1")),
            ],
        )
        .unwrap();
    }

    #[test]
    pub fn build_vpcmpestrm() {
        let declarations = parse(r#"// Autogenerated using stratification.
        requires "x86-configuration.k"
        
        module VPCMPESTRM-XMM-XMM-IMM8
          imports X86-CONFIGURATION
        
          // Find Limit Index
          rule <k>
            execinstr (vpcmpestrm Imm8:Imm, Xmm2:Xmm, Xmm1:Xmm,  .Operands) => 
              execinstr (vpcmpestrm 
                  handleImmediateWithSignExtend(Imm8, 8, 8), 
                  getRegisterValue(Xmm2, RSMap), 
                  getRegisterValue(Xmm1, RSMap),
                  findLimitIndexE(getRegisterValue(Xmm2, RSMap), getRegisterValue(%rdx, RSMap), handleImmediateWithSignExtend(Imm8, 8, 8)),   
                  findLimitIndexE(getRegisterValue(Xmm1, RSMap), getRegisterValue(%rax, RSMap), handleImmediateWithSignExtend(Imm8, 8, 8)),   
                  .Operands) 
          ...</k>
          <regstate> RSMap </regstate>
        
           // Find data size and interpretation
          rule <k>
            execinstr (vpcmpestrm Imm8:MInt,  Value2:MInt, Value1:MInt, Limit2:MInt, Limit1:MInt, .Operands) => 
              execinstr (vpcmpestrm Imm8,  Value2, Value1, Limit2, Limit1,
                  #ifMInt eqMInt(extractMInt(Imm8, 7, 8), mi(1, 1)) #then mi(8,8) #else mi(8, 16) #fi, 
                  extractMInt(Imm8, 6, 7),  .Operands)
          ...</k>
        
        
          // Aggregation operation
          rule <k>
            execinstr (vpcmpestrm Imm8:MInt,  Value2:MInt, Value1:MInt, Limit2:MInt, Limit1:MInt, NumElems:MInt, SignedOrUnsigned:MInt, .Operands) => 
              execinstr (vpcmpestrm Imm8,  Value2, Value1, Limit2, Limit1,  NumElems, SignedOrUnsigned, equalAnyImpl(Value2, Value1, Limit2, Limit1, uvalueMInt(NumElems), SignedOrUnsigned), .Operands)
          ...</k>
            requires eqMInt(extractMInt(Imm8, 4, 6), mi(2, 0))
            
          rule <k>
            execinstr (vpcmpestrm Imm8:MInt,  Value2:MInt, Value1:MInt, Limit2:MInt, Limit1:MInt, NumElems:MInt, SignedOrUnsigned:MInt, .Operands) => 
              execinstr (vpcmpestrm Imm8,  Value2, Value1, Limit2, Limit1,  NumElems, SignedOrUnsigned, rangeImpl(Value2, Value1, Limit2, Limit1, uvalueMInt(NumElems), SignedOrUnsigned), .Operands)
          ...</k>
            requires eqMInt(extractMInt(Imm8, 4, 6), mi(2, 1))
        
          rule <k>
            execinstr (vpcmpestrm Imm8:MInt,  Value2:MInt, Value1:MInt, Limit2:MInt, Limit1:MInt, NumElems:MInt, SignedOrUnsigned:MInt, .Operands) => 
              execinstr (vpcmpestrm Imm8,  Value2, Value1, Limit2, Limit1,  NumElems, SignedOrUnsigned, equalEachImpl(Value2, Value1, Limit2, Limit1, uvalueMInt(NumElems), SignedOrUnsigned), .Operands)
          ...</k>
            requires eqMInt(extractMInt(Imm8, 4, 6), mi(2, 2))
        
          rule <k>
            execinstr (vpcmpestrm Imm8:MInt,  Value2:MInt, Value1:MInt, Limit2:MInt, Limit1:MInt, NumElems:MInt, SignedOrUnsigned:MInt, .Operands) => 
              execinstr (vpcmpestrm Imm8,  Value2, Value1, Limit2, Limit1,  NumElems, SignedOrUnsigned, equalOrderedImpl(Value2, Value1, Limit2, Limit1, uvalueMInt(NumElems), SignedOrUnsigned), .Operands)
          ...</k>
            requires eqMInt(extractMInt(Imm8, 4, 6), mi(2, 3) )   
        
          // Polarity
          rule <k>
            execinstr (vpcmpestrm Imm8:MInt,  Value2:MInt, Value1:MInt, Limit2:MInt, Limit1:MInt, NumElems:MInt, SignedOrUnsigned:MInt, IntRes1:MInt, .Operands) => 
              execinstr (vpcmpestrm Imm8,  Value2, Value1, Limit2, Limit1,  NumElems, 
                  SignedOrUnsigned, IntRes1, 
                  polarityImpl(IntRes1, Imm8, uvalueMInt(NumElems), Limit2), .Operands)
          ...</k>
              
          // Output Selection
        
          rule <k>
            execinstr (vpcmpestrm Imm8:MInt,  Value2:MInt, Value1:MInt, Limit2:MInt, Limit1:MInt, NumElems:MInt, SignedOrUnsigned:MInt, IntRes1:MInt, IntRes2:MInt, .Operands) => 
              setRegisterValue(concatenateMInt(mi(128 -Int uvalueMInt(NumElems),  0), IntRes2), %xmm0) ~>
              setFlag(
                  {#ifMInt eqMInt(IntRes2, mi(bitwidthMInt(IntRes2), 0)) #then mi(1,0) #else mi(1,1) #fi}:>MInt 
                  , "CF") ~>
              setFlag(#ifMInt ultMInt(Limit2, NumElems) #then mi(1,1) #else mi(1,0) #fi, "ZF") ~>
              setFlag(#ifMInt ultMInt(Limit1, NumElems) #then mi(1,1) #else mi(1,0) #fi, "SF") ~>
              setFlag(extractMask(IntRes2, 1, 0), "OF") ~>
              setFlag(mi(1,0), "AF") ~>
              setFlag(mi(1,0), "PF") 
          ...</k>
            requires eqMInt(extractMInt(Imm8, 1, 2), mi(1, 0)) 
        
          rule <k>
            execinstr (vpcmpestrm Imm8:MInt,  Value2:MInt, Value1:MInt, Limit2:MInt, Limit1:MInt, NumElems:MInt, SignedOrUnsigned:MInt, IntRes1:MInt, IntRes2:MInt, .Operands) => 
              setRegisterValue(expandMask(IntRes2), %xmm0) ~>
              setFlag(
                  {#ifMInt eqMInt(IntRes2, mi(bitwidthMInt(IntRes2), 0)) #then mi(1,0) #else mi(1,1) #fi}:>MInt 
                  , "CF") ~>
              setFlag(#ifMInt ultMInt(Limit2, NumElems) #then mi(1,1) #else mi(1,0) #fi, "ZF") ~>
              setFlag(#ifMInt ultMInt(Limit1, NumElems) #then mi(1,1) #else mi(1,0) #fi, "SF") ~>
              setFlag(extractMask(IntRes2, 1, 0), "OF") ~>
              setFlag(mi(1,0), "AF") ~>
              setFlag(mi(1,0), "PF") 
          ...</k>
            requires eqMInt(extractMInt(Imm8, 1, 2), mi(1, 1) )
              
        endmodule
        "#).unwrap();
        let _kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from(r#"vpcmpestrm"#)),
            &[
                TokenTree::List {
                    kind: ListKind::Compose,
                    head: Box::new(TokenTree::Dollarydoo),
                    tail: Box::new(TokenTree::String(String::from("%virt:Imm:0"))),
                },
                TokenTree::String(String::from("%xmm0")),
                TokenTree::String(String::from("%xmm1")),
            ],
        )
        .unwrap();
    }

    #[test]
    pub fn build_shlw_r16_one() {
        let declarations = parse(r#"// Autogenerated using stratification.
        requires "x86-configuration.k"
        
        module SHLW-R16-ONE
          imports X86-CONFIGURATION
        
          rule <k>
            execinstr (shlw $0x1, R2:R16,  .Operands) => .
          ...</k>
            <regstate>
        RSMap:Map => updateMap(RSMap,
        convToRegKeys(R2) |-> concatenateMInt( extractMInt( getParentValue(R2, RSMap), 0, 48), extractMInt( shiftLeftMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R2, RSMap), 48, 64)), uvalueMInt(mi(17, 1))), 1, 17))
        
        "CF" |-> extractMInt( shiftLeftMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R2, RSMap), 48, 64)), uvalueMInt(mi(17, 1))), 0, 1)
        
        "PF" |-> (#ifMInt (notBool (((((((eqMInt( extractMInt( shiftLeftMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R2, RSMap), 48, 64)), uvalueMInt(mi(17, 1))), 16, 17), mi(1, 1)) xorBool eqMInt( extractMInt( shiftLeftMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R2, RSMap), 48, 64)), uvalueMInt(mi(17, 1))), 15, 16), mi(1, 1))) xorBool eqMInt( extractMInt( shiftLeftMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R2, RSMap), 48, 64)), uvalueMInt(mi(17, 1))), 14, 15), mi(1, 1))) xorBool eqMInt( extractMInt( shiftLeftMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R2, RSMap), 48, 64)), uvalueMInt(mi(17, 1))), 13, 14), mi(1, 1))) xorBool eqMInt( extractMInt( shiftLeftMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R2, RSMap), 48, 64)), uvalueMInt(mi(17, 1))), 12, 13), mi(1, 1))) xorBool eqMInt( extractMInt( shiftLeftMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R2, RSMap), 48, 64)), uvalueMInt(mi(17, 1))), 11, 12), mi(1, 1))) xorBool eqMInt( extractMInt( shiftLeftMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R2, RSMap), 48, 64)), uvalueMInt(mi(17, 1))), 10, 11), mi(1, 1))) xorBool eqMInt( extractMInt( shiftLeftMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R2, RSMap), 48, 64)), uvalueMInt(mi(17, 1))), 9, 10), mi(1, 1)))) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "AF" |-> (undefMInt)
        
        "ZF" |-> (#ifMInt eqMInt( extractMInt( shiftLeftMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R2, RSMap), 48, 64)), uvalueMInt(mi(17, 1))), 1, 17), mi(16, 0)) #then mi(1, 1) #else mi(1, 0) #fi)
        
        "SF" |-> extractMInt( shiftLeftMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R2, RSMap), 48, 64)), uvalueMInt(mi(17, 1))), 1, 2)
        
        "OF" |-> (#ifMInt (eqMInt( extractMInt( shiftLeftMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R2, RSMap), 48, 64)), uvalueMInt(mi(17, 1))), 0, 1), mi(1, 1)) xorBool eqMInt( extractMInt( shiftLeftMInt( concatenateMInt( mi(1, 0), extractMInt( getParentValue(R2, RSMap), 48, 64)), uvalueMInt(mi(17, 1))), 1, 2), mi(1, 1))) #then mi(1, 1) #else mi(1, 0) #fi)
        )
        
            </regstate>
            
        endmodule
        
        module SHLW-R16-ONE-SEMANTICS
          imports SHLW-R16-ONE
        endmodule
        "#).unwrap();
        let _kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from(r#"shlw"#)),
            &[
                TokenTree::List {
                    kind: ListKind::Compose,
                    head: Box::new(TokenTree::Dollarydoo),
                    tail: Box::new(TokenTree::List {
                        kind: ListKind::Compose,
                        head: Box::new(TokenTree::Hex(1)),
                        tail: Box::new(TokenTree::Nil),
                    }),
                },
                TokenTree::String(String::from("%virt:R16:0")),
            ],
        )
        .unwrap();
    }

    #[test]
    pub fn build_with_virt_ymm3() {
        let declarations = parse(
            r#"// Autogenerated using stratification.
        requires "x86-configuration.k"
        
        module VPBLENDW-YMM-YMM-YMM-IMM8
          imports X86-CONFIGURATION
        
          rule <k>
            execinstr (vpblendw Imm8:Imm, R2:Ymm, R3:Ymm, R4:Ymm,  .Operands) => .
          ...</k>
            <regstate>
        RSMap:Map => updateMap(RSMap,
        convToRegKeys(R4) |-> mi(1, 0)
        )
        
            </regstate>
            
        endmodule
        
        module VPBLENDW-YMM-YMM-YMM-IMM8-SEMANTICS
          imports VPBLENDW-YMM-YMM-YMM-IMM8
        endmodule
        "#,
        )
        .unwrap();
        let kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from(r#"vpblendw"#)),
            &[
                TokenTree::List {
                    kind: ListKind::Compose,
                    head: Box::new(TokenTree::Dollarydoo),
                    tail: Box::new(TokenTree::List {
                        kind: ListKind::Compose,
                        head: Box::new(TokenTree::Hex(1)),
                        tail: Box::new(TokenTree::Nil),
                    }),
                },
                TokenTree::String(String::from("%virt:Ymm:1")),
                TokenTree::String(String::from("%virt:Ymm:2")),
                TokenTree::String(String::from("%virt:Ymm:3")),
            ],
        )
        .unwrap();

        assert_eq!(kz3.map.len(), 1);
    }

    #[test]
    pub fn build_bsfl_r32_r32() {
        let declarations = parse(
            r#"// Autogenerated using stratification.
        requires "x86-configuration.k"
        
        module BSFL-R32-R32
          imports X86-CONFIGURATION
        
          rule <k>
            execinstr (bsfl R1:R32, R2:R32,  .Operands) =>  .
          ...</k>
           <regstate>
        RSMap:Map => updateMap(RSMap,
          convToRegKeys(R2) |-> (createUndefMInt(bitwidthMInt(getRegisterValue(R2, RSMap))))
          "ZF" |-> mi(1,1)
          "SF" |-> (undefMInt)
          "CF" |-> (undefMInt)
          "OF" |-> (undefMInt)
          "PF" |-> (undefMInt)
          "AF" |-> (undefMInt)
          )
           </regstate>
            requires eqMInt(getRegisterValue(R1, RSMap), mi(32, 0))
        
        
          rule <k>
            execinstr (bsfl R1:R32, R2:R32,  .Operands) =>  .
          ...</k>
           <regstate>
        RSMap:Map => updateMap(RSMap,
          convToRegKeys(R2) |-> mi(64, scanForward(getRegisterValue(R1, RSMap), 31, 32))
          "ZF" |-> mi(1,0)
          "SF" |-> (undefMInt)
          "CF" |-> (undefMInt)
          "OF" |-> (undefMInt)
          "PF" |-> (undefMInt)
          "AF" |-> (undefMInt)
          )
           </regstate>
            requires notBool eqMInt(getRegisterValue(R1, RSMap), mi(32, 0))
        
            
        endmodule
        "#,
        )
        .unwrap();
        let kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from(r#"bsfl"#)),
            &[
                TokenTree::String(String::from("%virt:R32:0")),
                TokenTree::String(String::from("%virt:R32:1")),
            ],
        )
        .unwrap();

        println!("{kz3:?}");

        assert_eq!(kz3.map.len(), 7);
    }

    #[test]
    pub fn build_jna_imm8() {
        let declarations = parse(
            r#"requires "x86-configuration.k"
        module JNA-REL8
          imports X86-CONFIGURATION
          imports X86-FLAG-CHECS-SYNTAX
        
          rule <k> 
            execinstr (jna Imm8:Imm, .Operands) => .
          ...</k>
              <regstate> RSMap => updateMap(RSMap, ("RIP" |->
                    addMInt({RSMap["RIP"]}:>MInt, handleImmediateWithSignExtend(Imm8,
                        8, 64))))
              </regstate>
                requires eqMInt({RSMap["ZF"]}:>MInt, mi(1, 1)) orBool  eqMInt({RSMap["CF"]}:>MInt, mi(1, 1))
        
          rule <k> 
            execinstr (jna Imm8:Imm, .Operands) => .
          ...</k>
              <regstate> RSMap:Map </regstate> 
                requires notBool eqMInt({RSMap["ZF"]}:>MInt, mi(1, 1)) andBool notBool eqMInt({RSMap["CF"]}:>MInt, mi(1, 1))
        endmodule
        "#,
        )
        .unwrap();
        let kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from(r#"jna"#)),
            &[TokenTree::List {
                kind: ListKind::Compose,
                head: Box::new(TokenTree::Dollarydoo),
                tail: Box::new(TokenTree::List {
                    kind: ListKind::Compose,
                    head: Box::new(TokenTree::Hex(1)),
                    tail: Box::new(TokenTree::Nil),
                }),
            }],
        )
        .unwrap();

        println!("{kz3:?}");

        assert_eq!(kz3.map.len(), 1);
    }

    #[test]
    pub fn build_mulx() {
        let declarations = parse(r#"
            requires "x86-configuration.k"
            
            module MULXL-R32-R32-M32
              imports X86-CONFIGURATION
              rule <k>
                execinstr (mulx:Opcode M:Mem, R2:R32, R3:R32,  .Operands) => execinstr (mulxl:Opcode M:Mem, R2:R32, R3:R32,  .Operands)
              ...</k>
            
              context execinstr(mulxl:Opcode HOLE:Mem, R2:R32, R3:R32,  .Operands) [result(MemOffset)]
              
              rule <k>
                execinstr (mulxl:Opcode memOffset( MemOff:MInt):MemOffset, R2:R32, R3:R32,  .Operands) =>
                  loadFromMemory( MemOff, 32) ~>
                  execinstr (mulxl memOffset( MemOff), R2, R3,  .Operands)
              ...</k>
                <regstate> RSMap:Map </regstate>
                      
              rule <k>
                memLoadValue(Mem32:MInt):MemLoadValue ~> execinstr (mulxl:Opcode memOffset( MemOff:MInt):MemOffset, R2:R32, R3:R32,  .Operands) =>
                  .
              ...</k>
                <regstate>
                  RSMap:Map => updateMap(RSMap,
            convToRegKeys(R2) |-> concatenateMInt( mi(32, 0), extractMInt( mulMInt( concatenateMInt( mi(32, 0), extractMInt( getParentValue(%rdx, RSMap), 32, 64)), concatenateMInt( mi(32, 0), Mem32)), 32, 64))
            
            convToRegKeys(R3) |-> concatenateMInt( mi(32, 0), extractMInt( mulMInt( concatenateMInt( mi(32, 0), extractMInt( getParentValue(%rdx, RSMap), 32, 64)), concatenateMInt( mi(32, 0), Mem32)), 0, 32))
                  )
                </regstate>
            endmodule            
        "#).unwrap();
        let kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from(r#"mulxl"#)),
            &[
                f(
                    "memOffset",
                    [f("z3_bitvec", [TokenTree::String(String::from("%r9")), TokenTree::Num(64)])],
                ),
                TokenTree::String(String::from("%virt:R32:1")),
                TokenTree::String(String::from("%virt:R32:2")),
            ],
        )
        .unwrap();

        println!("{kz3:?}");

        // Ordering here matters because both %virts could refer to the same register
        assert_eq!(kz3.map[0].0, StorageLocation::Reg(String::from("%virt:R64:1")));
        assert_eq!(kz3.map[1].0, StorageLocation::Reg(String::from("%virt:R64:2")));
    }
    #[test]
    pub fn build_xchgw() {
        let declarations = parse(r#"
        // Autogenerated using stratification.
        requires "x86-configuration.k"
        
        module XCHGW-R16-M16
          imports X86-CONFIGURATION
        
          context execinstr(xchgw:Opcode HOLE:Mem, R2:R16,  .Operands) [result(MemOffset)]
          
          rule <k>
            execinstr (xchgw:Opcode memOffset( MemOff:MInt):MemOffset, R2:R16,  .Operands) =>
              loadFromMemory( MemOff, 16) ~>
              execinstr (xchgw memOffset( MemOff), R2,  .Operands)
          ...</k>
            <regstate> RSMap:Map </regstate>
                  
          rule <k>
            memLoadValue(Mem16:MInt):MemLoadValue ~> execinstr (xchgw:Opcode memOffset( MemOff:MInt):MemOffset, R2:R16,  .Operands) =>
              
                    storeToMemory(
                      extractMInt( getParentValue(R2, RSMap), 48, 64),
                      MemOff,
                      16
                    )
                  
          ...</k>
            <regstate>
              RSMap:Map => updateMap(RSMap,
        convToRegKeys(R2) |-> concatenateMInt( extractMInt( getParentValue(R2, RSMap), 0, 48), Mem16)
              )
            </regstate>
        endmodule                  
        "#).unwrap();
        let kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from(r#"xchgw"#)),
            &[
                f(
                    "memOffset",
                    [f("z3_bitvec", [TokenTree::String(String::from("%r9")), TokenTree::Num(64)])],
                ),
                TokenTree::String(String::from("%virt:R16:1")),
            ],
        )
        .unwrap();

        println!("{kz3:?}");
    }

    #[test]
    pub fn build_pushq() {
        let declarations = parse(
            r#"
        requires "x86-configuration.k"
        
        module PUSHQ-R64
        imports X86-CONFIGURATION

        rule <k> 
            execinstr (pushq R1:R64, .Operands) =>
            storeToMemory(
                getRegisterValue(R1, RSMap), 
                subMInt(getRegisterValue(%rsp, RSMap), mi(64, 8)), 
                64)  ~>  
            decRSPInBytes(8)
        ...</k>
        <regstate> RSMap </regstate>
        endmodule
        "#,
        )
        .unwrap();
        let kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from(r#"pushq"#)),
            &[TokenTree::String(String::from("%virt:R64:0"))],
        )
        .unwrap();

        println!("{kz3:?}");
    }

    #[test]
    pub fn build_popq() {
        let declarations = parse(
            r#"
        requires "x86-configuration.k"

        /*@
        Pop R: 
        1. RSP = RSP + 8
        2. ValTostore = *(RSP - 8)
        3. R =  ValTostore)
        */  
        module POPQ-R64
        imports X86-CONFIGURATION

        rule <k> 
            execinstr (popq R1:R64, .Operands) =>
            incRSPInBytes(8) ~>
            setRegisterValue(
                loadFromMemory(getRegisterValue(%rsp, RSMap), 64), 
                R1) 
        ...</k>
        <regstate> RSMap </regstate>
        endmodule

        "#,
        )
        .unwrap();
        let kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from(r#"popq"#)),
            &[TokenTree::String(String::from("%virt:R64:0"))],
        )
        .unwrap();

        println!("{kz3:?}");
    }

    #[test]
    pub fn build_loope() {
        let declarations = parse(r#"
        requires "x86-configuration.k"

        module LOOPE-REL8
        imports X86-CONFIGURATION
        imports X86-FLAG-CHECS-SYNTAX

        rule <k> 
            execinstr (loope Imm8:Imm, .Operands) => execinstr (loope Imm8, subMInt(getRegisterValue(%rcx, RSMap), mi(64, 1)), .Operands)
        ...</k>
            <regstate> RSMap </regstate>

        rule <k> 
            execinstr (loope Imm8:Imm, Count:MInt,  .Operands) => .
        ...</k>
            <regstate> RSMap => updateMap(RSMap, 
                ("RIP" |-> addMInt({RSMap["RIP"]}:>MInt, handleImmediateWithSignExtend(Imm8, 8, 64)))
                ("RCX" |-> Count)
                )
            </regstate>
                requires notBool eqMInt(Count, mi(bitwidthMInt(Count), 0))
                andBool eqMInt({RSMap["ZF"]}:>MInt, mi(1, 1))

        rule <k> 
            execinstr (loope Imm8:Imm, Count:MInt,  .Operands) => .
        ...</k>
            <regstate> RSMap => updateMap(RSMap, 
                ("RCX" |-> Count)
                )
            </regstate>
                requires eqMInt(Count, mi(bitwidthMInt(Count), 0))
                orBool notBool eqMInt({RSMap["ZF"]}:>MInt, mi(1, 1))

        endmodule
        "#).unwrap();
        let kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from(r#"loope"#)),
            &[TokenTree::List {
                kind: ListKind::Compose,
                head: Box::new(TokenTree::Dollarydoo),
                tail: Box::new(TokenTree::List {
                    kind: ListKind::Compose,
                    head: Box::new(TokenTree::Hex(1)),
                    tail: Box::new(TokenTree::Nil),
                }),
            }],
        )
        .unwrap();

        println!("{kz3:?}");
    }

    #[test]
    pub fn build_vmpsadbw_ymm_ymm_m256_imm8() {
        // Make sure an incorrectly typed execinstr gives `None`.
        let declarations = parse(r#"
        // Autogenerated using stratification.
requires "x86-configuration.k"

module VMPSADBW-YMM-YMM-M256-IMM8
  imports X86-CONFIGURATION

  context execinstr(vmpsadbw:Opcode (_:Imm,  HOLE:Mem, R3:Xmm, R4:Xmm, .Operands):Operands) [result(MemOffset)]

  rule <k>
    execinstr (vmpsadbw I:Imm, memOffset( MemOff:MInt):MemOffset, R3:Xmm, R4:Xmm, .Operands) => 
      loadFromMemory( MemOff, 256) ~> execinstr (vmpsadbw I, memOffset( MemOff), R3:Xmm, R4:Xmm, .Operands)                 
  ...</k>


  rule <k>
    memLoadValue(MemVal:MInt):MemLoadValue ~>
    execinstr (vmpsadbw Imm8:Imm, memOffset( MemOff:MInt):MemOffset, R3:Ymm, R4:Ymm,  .Operands) => 
      execinstr (vmpsadbw
        //Low slices  
        selectSliceMPSAD(MemVal,
          extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 6, 8), 7 , 0 ),
        selectSliceMPSAD(MemVal,
          extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 6, 8), 15, 8 ),
        selectSliceMPSAD(MemVal,
          extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 6, 8), 23, 16),
        selectSliceMPSAD(MemVal,
          extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 6, 8), 31, 24),

        selectSliceMPSAD(getRegisterValue(R3, RSMap),
          extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 5, 6), 7 ,  0),
        selectSliceMPSAD(getRegisterValue(R3, RSMap),
          extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 5, 6), 15,  8),
        selectSliceMPSAD(getRegisterValue(R3, RSMap),
          extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 5, 6), 23, 16),
        selectSliceMPSAD(getRegisterValue(R3, RSMap),
          extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 5, 6), 31, 24),
        selectSliceMPSAD(getRegisterValue(R3, RSMap),
          extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 5, 6), 39, 32),
        selectSliceMPSAD(getRegisterValue(R3, RSMap),
          extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 5, 6), 47, 40),
        selectSliceMPSAD(getRegisterValue(R3, RSMap),
          extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 5, 6), 55, 48),
        selectSliceMPSAD(getRegisterValue(R3, RSMap),
          extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 5, 6), 63, 56),
        selectSliceMPSAD(getRegisterValue(R3, RSMap),
          extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 5, 6), 71, 64),
        selectSliceMPSAD(getRegisterValue(R3, RSMap),
          extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 5, 6), 79, 72),
        selectSliceMPSAD(getRegisterValue(R3, RSMap),
          extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 5, 6), 87, 80),

        //High slices  
        selectSliceMPSAD(MemVal,
            extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 3, 5), 7 +Int
            128, 0 +Int 128),
        selectSliceMPSAD(MemVal,
            extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 3, 5), 15+Int
            128, 8 +Int 128),
        selectSliceMPSAD(MemVal,
            extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 3, 5), 23+Int
            128, 16+Int 128),
        selectSliceMPSAD(MemVal,
            extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 3, 5), 31+Int
            128, 24+Int 128),

        selectSliceMPSAD(getRegisterValue(R3, RSMap), 
            extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 2, 3), 7
            +Int 128,  0 +Int 128),
        selectSliceMPSAD(getRegisterValue(R3, RSMap), 
            extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 2, 3), 15
            +Int 128,  8 +Int 128),
        selectSliceMPSAD(getRegisterValue(R3, RSMap), 
            extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 2, 3), 23
            +Int 128, 16 +Int 128),
        selectSliceMPSAD(getRegisterValue(R3, RSMap), 
            extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 2, 3), 31
            +Int 128, 24 +Int 128),
        selectSliceMPSAD(getRegisterValue(R3, RSMap), 
            extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 2, 3), 39
            +Int 128, 32 +Int 128),
        selectSliceMPSAD(getRegisterValue(R3, RSMap), 
            extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 2, 3), 47
            +Int 128, 40 +Int 128),
        selectSliceMPSAD(getRegisterValue(R3, RSMap), 
            extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 2, 3), 55
            +Int 128, 48 +Int 128),
        selectSliceMPSAD(getRegisterValue(R3, RSMap), 
            extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 2, 3), 63
            +Int 128, 56 +Int 128),
        selectSliceMPSAD(getRegisterValue(R3, RSMap), 
            extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 2, 3), 71
            +Int 128, 64 +Int 128),
        selectSliceMPSAD(getRegisterValue(R3, RSMap), 
            extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 2, 3), 79
            +Int 128, 72 +Int 128),
        selectSliceMPSAD(getRegisterValue(R3, RSMap), 
            extractMInt(handleImmediateWithSignExtend(Imm8, 8, 8), 2, 3), 87
            +Int 128, 80 +Int 128),

        R4:Ymm, 
        .Operands)
  ...</k>   
    <regstate> RSMap </regstate>


  rule <k> 
    execinstr (vmpsadbw 
        LowSrcByte0:MInt, LowSrcByte1:MInt, LowSrcByte2:MInt, LowSrcByte3:MInt,
        LowDestByte0:MInt, LowDestByte1:MInt, LowDestByte2:MInt, LowDestByte3:MInt,
        LowDestByte4:MInt, LowDestByte5:MInt, LowDestByte6:MInt, LowDestByte7:MInt,
        LowDestByte8:MInt, LowDestByte9:MInt, LowDestByte10:MInt,

        HighSrcByte0:MInt, HighSrcByte1:MInt, HighSrcByte2:MInt, HighSrcByte3:MInt,
        HighDestByte0:MInt, HighDestByte1:MInt, HighDestByte2:MInt, HighDestByte3:MInt,
        HighDestByte4:MInt, HighDestByte5:MInt, HighDestByte6:MInt, HighDestByte7:MInt,
        HighDestByte8:MInt, HighDestByte9:MInt, HighDestByte10:MInt,
        R4:Ymm,  .Operands) =>
  setRegisterValue(
  concatenateMInt(
    concatenateMInt(

      concatenateMInt(    
        concatenateMInt(
          addMInt(
            addMInt(
              absoluteUnsignedDifference(HighDestByte7, HighSrcByte0),
              absoluteUnsignedDifference(HighDestByte8, HighSrcByte1)),
            addMInt(
              absoluteUnsignedDifference(HighDestByte9, HighSrcByte2),
              absoluteUnsignedDifference(HighDestByte10, HighSrcByte3))
          ),
          addMInt(
            addMInt(
              absoluteUnsignedDifference(HighDestByte6, HighSrcByte0),
              absoluteUnsignedDifference(HighDestByte7, HighSrcByte1)),
            addMInt(
              absoluteUnsignedDifference(HighDestByte8, HighSrcByte2),
              absoluteUnsignedDifference(HighDestByte9, HighSrcByte3))
          )),
        concatenateMInt(
          addMInt(
            addMInt(
              absoluteUnsignedDifference(HighDestByte5, HighSrcByte0),
              absoluteUnsignedDifference(HighDestByte6, HighSrcByte1)),
            addMInt(
              absoluteUnsignedDifference(HighDestByte7, HighSrcByte2),
              absoluteUnsignedDifference(HighDestByte8, HighSrcByte3))
          ),
          addMInt(
            addMInt(
              absoluteUnsignedDifference(HighDestByte4, HighSrcByte0),
              absoluteUnsignedDifference(HighDestByte5, HighSrcByte1)),
            addMInt(
              absoluteUnsignedDifference(HighDestByte6, HighSrcByte2),
              absoluteUnsignedDifference(HighDestByte7, HighSrcByte3))
          ))
        ),
     
      concatenateMInt(
        concatenateMInt(
          addMInt(
            addMInt(
              absoluteUnsignedDifference(HighDestByte3, HighSrcByte0),
              absoluteUnsignedDifference(HighDestByte4, HighSrcByte1)),
            addMInt(
              absoluteUnsignedDifference(HighDestByte5, HighSrcByte2),
              absoluteUnsignedDifference(HighDestByte6, HighSrcByte3))
          ),
          addMInt(
            addMInt(
              absoluteUnsignedDifference(HighDestByte2, HighSrcByte0),
              absoluteUnsignedDifference(HighDestByte3, HighSrcByte1)),
            addMInt(
              absoluteUnsignedDifference(HighDestByte4, HighSrcByte2),
              absoluteUnsignedDifference(HighDestByte5, HighSrcByte3))
          )),
        concatenateMInt(
          addMInt(
            addMInt(
              absoluteUnsignedDifference(HighDestByte1, HighSrcByte0),
              absoluteUnsignedDifference(HighDestByte2, HighSrcByte1)),
            addMInt(
              absoluteUnsignedDifference(HighDestByte3, HighSrcByte2),
              absoluteUnsignedDifference(HighDestByte4, HighSrcByte3))
          ),
          addMInt(
            addMInt(
              absoluteUnsignedDifference(HighDestByte0, HighSrcByte0),
              absoluteUnsignedDifference(HighDestByte1, HighSrcByte1)),
            addMInt(
              absoluteUnsignedDifference(HighDestByte2, HighSrcByte2),
              absoluteUnsignedDifference(HighDestByte3, HighSrcByte3))
          ))
      )),

      //Lower 
      
    concatenateMInt(

      concatenateMInt(    
        concatenateMInt(
          addMInt(
            addMInt(
              absoluteUnsignedDifference(LowDestByte7, LowSrcByte0),
              absoluteUnsignedDifference(LowDestByte8, LowSrcByte1)),
            addMInt(
              absoluteUnsignedDifference(LowDestByte9, LowSrcByte2),
              absoluteUnsignedDifference(LowDestByte10, LowSrcByte3))
          ),
          addMInt(
            addMInt(
              absoluteUnsignedDifference(LowDestByte6, LowSrcByte0),
              absoluteUnsignedDifference(LowDestByte7, LowSrcByte1)),
            addMInt(
              absoluteUnsignedDifference(LowDestByte8, LowSrcByte2),
              absoluteUnsignedDifference(LowDestByte9, LowSrcByte3))
          )),
        concatenateMInt(
          addMInt(
            addMInt(
              absoluteUnsignedDifference(LowDestByte5, LowSrcByte0),
              absoluteUnsignedDifference(LowDestByte6, LowSrcByte1)),
            addMInt(
              absoluteUnsignedDifference(LowDestByte7, LowSrcByte2),
              absoluteUnsignedDifference(LowDestByte8, LowSrcByte3))
          ),
          addMInt(
            addMInt(
              absoluteUnsignedDifference(LowDestByte4, LowSrcByte0),
              absoluteUnsignedDifference(LowDestByte5, LowSrcByte1)),
            addMInt(
              absoluteUnsignedDifference(LowDestByte6, LowSrcByte2),
              absoluteUnsignedDifference(LowDestByte7, LowSrcByte3))
          ))
        ),
     
      concatenateMInt(
        concatenateMInt(
          addMInt(
            addMInt(
              absoluteUnsignedDifference(LowDestByte3, LowSrcByte0),
              absoluteUnsignedDifference(LowDestByte4, LowSrcByte1)),
            addMInt(
              absoluteUnsignedDifference(LowDestByte5, LowSrcByte2),
              absoluteUnsignedDifference(LowDestByte6, LowSrcByte3))
          ),
          addMInt(
            addMInt(
              absoluteUnsignedDifference(LowDestByte2, LowSrcByte0),
              absoluteUnsignedDifference(LowDestByte3, LowSrcByte1)),
            addMInt(
              absoluteUnsignedDifference(LowDestByte4, LowSrcByte2),
              absoluteUnsignedDifference(LowDestByte5, LowSrcByte3))
          )),
        concatenateMInt(
          addMInt(
            addMInt(
              absoluteUnsignedDifference(LowDestByte1, LowSrcByte0),
              absoluteUnsignedDifference(LowDestByte2, LowSrcByte1)),
            addMInt(
              absoluteUnsignedDifference(LowDestByte3, LowSrcByte2),
              absoluteUnsignedDifference(LowDestByte4, LowSrcByte3))
          ),
          addMInt(
            addMInt(
              absoluteUnsignedDifference(LowDestByte0, LowSrcByte0),
              absoluteUnsignedDifference(LowDestByte1, LowSrcByte1)),
            addMInt(
              absoluteUnsignedDifference(LowDestByte2, LowSrcByte2),
              absoluteUnsignedDifference(LowDestByte3, LowSrcByte3))
          ))
      ))
      
      
      ) , R4)

  ...</k>
endmodule

module VMPSADBW-YMM-YMM-YMM-IMM8-SEMANTICS
  imports VMPSADBW-YMM-YMM-YMM-IMM8
endmodule
        "#).unwrap();
        let kz3 = Kz3::expand(
            &declarations,
            &TokenTree::String(String::from(r#"vmpsadbw"#)),
            &[
                TokenTree::List {
                    kind: ListKind::Compose,
                    head: Box::new(TokenTree::Dollarydoo),
                    tail: Box::new(TokenTree::List {
                        kind: ListKind::Compose,
                        head: Box::new(TokenTree::Hex(1)),
                        tail: Box::new(TokenTree::Nil),
                    }),
                },
                f(
                    "memOffset",
                    [f("z3_bitvec", [TokenTree::String(String::from("%r9")), TokenTree::Num(64)])],
                ),
                TokenTree::String(String::from("%virt:Xmm:0")),
                TokenTree::String(String::from("%virt:Xmm:1")),
            ],
        );

        assert!(kz3.is_none());
    }
}
