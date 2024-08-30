use std::collections::HashMap;
use std::ops::{AddAssign, Not};

use itertools::Itertools;
use kparser::z3::{Kz3, Kz3Converter, StorageLocation, Z3Node};
use liblisa::arch::x64::{GpReg, X64Arch, X64Reg, XmmReg};
use liblisa::arch::{Arch, Register};
use liblisa::encoding::dataflows::{AddrTerm, AddrTermCalculation, AddrTermSize, Dataflows, Dest, Inputs, Size, Source};
use liblisa::encoding::Encoding;
use liblisa::semantics::default::computation::SynthesizedComputation;
use liblisa::semantics::default::smtgen::{FilledLocation, Sizes, StorageLocations, Z3Model};
use liblisa::smt::{Dynamic, SatResult, SmtBV, SmtBool, SmtSolver};
use liblisa::state::Location;
use liblisa::utils::bitmap::GrowingBitmap;
use liblisa::value::ValueType;
use log::{debug, info, trace, warn};
use serde::{Deserialize, Serialize};

use crate::{Operand, RegType, SemanticEquivalence};

pub fn alias_to_full_reg(op: &str) -> &str {
    match op {
        "%al" | "%ah" | "%ax" | "%eax" | "%rax" => "RAX",
        "%bl" | "%bh" | "%bx" | "%ebx" | "%rbx" => "RBX",
        "%cl" | "%ch" | "%cx" | "%ecx" | "%rcx" => "RCX",
        "%dl" | "%dh" | "%dx" | "%edx" | "%rdx" => "RDX",
        "%sil" | "%si" | "%esi" | "%rsi" => "RSI",

        "%dil" | "%di" | "%edi" | "%rdi" => "RDI",

        "%spl" | "%sp" | "%esp" | "%rsp" => "RSP",

        "%bpl" | "%bp" | "%ebp" | "%rbp" => "RBP",

        "%r8b" | "%r8w" | "%r8d" | "%r8" => "R8",

        "%r9b" | "%r9w" | "%r9d" | "%r9" => "R9",

        "%r10b" | "%r10w" | "%r10d" | "%r10" => "R10",

        "%r11b" | "%r11w" | "%r11d" | "%r11" => "R11",

        "%r12b" | "%r12w" | "%r12d" | "%r12" => "R12",

        "%r13b" | "%r13w" | "%r13d" | "%r13" => "R13",

        "%r14b" | "%r14w" | "%r14d" | "%r14" => "R14",

        "%r15b" | "%r15w" | "%r15d" | "%r15" => "R15",

        "%rip" => "RIP",
        "%riz" => "RIZ",

        "%xmm0" => "YMM0",
        "%xmm1" => "YMM1",
        "%xmm2" => "YMM2",
        "%xmm3" => "YMM3",
        "%xmm4" => "YMM4",
        "%xmm5" => "YMM5",
        "%xmm6" => "YMM6",
        "%xmm7" => "YMM7",
        "%xmm8" => "YMM8",
        "%xmm9" => "YMM9",
        "%xmm10" => "YMM10",
        "%xmm11" => "YMM11",
        "%xmm12" => "YMM12",
        "%xmm13" => "YMM13",
        "%xmm14" => "YMM14",
        "%xmm15" => "YMM15",

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

        "%mm0" => "MM0",
        "%mm1" => "MM1",
        "%mm2" => "MM2",
        "%mm3" => "MM3",
        "%mm4" => "MM4",
        "%mm5" => "MM5",
        "%mm6" => "MM6",
        "%mm7" => "MM7",
        "%mm8" => "MM8",
        "%mm9" => "MM9",
        _ => unimplemented!("alias_to_full_reg({op})"),
    }
}

pub fn translate_variable_name_to_reg(original_name: &str, operands: &[(Operand, RegType)]) -> Option<(X64Reg, Size)> {
    let name = match original_name {
        "%virt:R64:0" | "%virt:R64:1" | "%virt:R64:2" => {
            let index = original_name.strip_prefix("%virt:R64:").unwrap().parse::<usize>().unwrap();
            let (node, reg_type) = &operands[index];

            trace!("{original_name} => {node:?} / {reg_type:?}");
            let Operand::Var(name) = node else {
                panic!("Expected {original_name} to be a Operand::Var, but found {node:?}")
            };
            alias_to_full_reg(name)
        },
        "%virt:R32:0" | "%virt:R32:1" | "%virt:R32:2" => {
            let index = original_name.strip_prefix("%virt:R32:").unwrap().parse::<usize>().unwrap();
            let (node, reg_type) = &operands[index];

            trace!("{original_name} => {node:?} / {reg_type:?}");
            let Operand::Var(name) = node else {
                panic!("Expected {original_name} to be a Operand::Var, but found {node:?}")
            };
            alias_to_full_reg(name)
        },
        "%virt:R16:0" | "%virt:R16:1" | "%virt:R16:2" => {
            let index = original_name.strip_prefix("%virt:R16:").unwrap().parse::<usize>().unwrap();
            let (node, reg_type) = &operands[index];

            trace!("{original_name} => {node:?} / {reg_type:?}");
            let Operand::Var(name) = node else {
                panic!("Expected {original_name} to be a Operand::Var, but found {node:?}")
            };
            alias_to_full_reg(name)
        },
        "%virt:R8:0" | "%virt:R8:1" | "%virt:R8:2" => {
            let index = original_name.strip_prefix("%virt:R8:").unwrap().parse::<usize>().unwrap();
            let (node, reg_type) = &operands[index];

            trace!("{original_name} => {node:?} / {reg_type:?}");
            let Operand::Var(name) = node else {
                panic!("Expected {original_name} to be a Operand::Var, but found {node:?}")
            };
            alias_to_full_reg(name)
        },
        "%virt:Rh:0" | "%virt:Rh:1" | "%virt:Rh:2" => {
            let index = original_name.strip_prefix("%virt:Rh:").unwrap().parse::<usize>().unwrap();
            let (node, reg_type) = &operands[index];

            trace!("{original_name} => {node:?} / {reg_type:?}");
            let Operand::Var(name) = node else {
                panic!("Expected {original_name} to be a Operand::Var, but found {node:?}")
            };
            alias_to_full_reg(name)
        },
        "%virt:Ymm:0" | "%virt:Ymm:1" | "%virt:Ymm:2" | "%virt:Ymm:3" => {
            let index = original_name.strip_prefix("%virt:Ymm:").unwrap().parse::<usize>().unwrap();
            let (node, reg_type) = &operands[index];

            trace!("{original_name} => {node:?} / {reg_type:?}");
            let Operand::Var(name) = node else {
                panic!("Expected {original_name} to be a Operand::Var, but found {node:?}")
            };
            alias_to_full_reg(name)
        },
        name => name,
    };

    let fixed_name = name.to_lowercase().replace("ymm", "xmm");
    X64Arch::iter_regs()
        .find(|reg| reg.to_string().to_lowercase() == fixed_name)
        .map(|reg| {
            let size = match original_name {
                "%virt:R64:0" | "%virt:R64:1" | "%virt:R64:2" => Size::new(0, 7),
                "%virt:R32:0" | "%virt:R32:1" | "%virt:R32:2" => Size::new(0, 3),
                "%virt:R16:0" | "%virt:R16:1" | "%virt:R16:2" => Size::new(0, 1),
                "%virt:R8:0" | "%virt:R8:1" | "%virt:R8:2" => Size::new(0, 0),
                "%virt:Rh:0" | "%virt:Rh:1" | "%virt:Rh:2" => Size::new(1, 1),
                _ => Size::new(0, reg.byte_size() - 1),
            };
            (reg, size)
        })
        .or_else(|| {
            Some(match name {
                mm if mm.starts_with("YMM") => (
                    X64Reg::Xmm(XmmReg::Reg(mm.strip_prefix("YMM").unwrap().parse().unwrap())),
                    Size::new(0, 31),
                ),
                "CF" => (X64Reg::GpReg(GpReg::RFlags), Size::new(0, 0)),
                "PF" => (X64Reg::GpReg(GpReg::RFlags), Size::new(1, 1)),
                "AF" => (X64Reg::GpReg(GpReg::RFlags), Size::new(2, 2)),
                "ZF" => (X64Reg::GpReg(GpReg::RFlags), Size::new(3, 3)),
                "SF" => (X64Reg::GpReg(GpReg::RFlags), Size::new(4, 4)),
                "OF" => (X64Reg::GpReg(GpReg::RFlags), Size::new(5, 5)),
                "addr0" | "addr1" | "addr2" => return None,
                "%rax" => (X64Reg::GpReg(GpReg::Rax), Size::new(0, 7)),
                "%eax" => (X64Reg::GpReg(GpReg::Rax), Size::new(0, 3)),
                "%ah" => (X64Reg::GpReg(GpReg::Rax), Size::new(1, 1)),
                "%al" => (X64Reg::GpReg(GpReg::Rax), Size::new(0, 0)),
                "RIZ" => (X64Reg::GpReg(GpReg::Riz), Size::qword()),
                // TODO: libLISA doesn't support the DF flag (but we should)
                "DF" => (X64Reg::GpReg(GpReg::Riz), Size::new(0, 0)),
                _ => panic!("Unable to find reg: {name:?}"),
            })
        })
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemAddr {
    pub offset: i64,
    pub sum_of: HashMap<(X64Reg, AddrTermSize, u8), usize>,
}

impl MemAddr {
    pub fn from_liblisa(mut offset: i64, inputs: &Inputs<X64Arch>, terms: &[AddrTerm]) -> MemAddr {
        let mut sum_of = HashMap::new();
        for (&term, source) in terms.iter().zip(inputs.iter()) {
            match *source {
                Source::Dest(Dest::Reg(reg, size)) => {
                    if !reg.is_zero() {
                        assert_eq!(size, Size::qword());
                        *sum_of
                            .entry((reg, term.primary.size, term.primary.shift.right()))
                            .or_insert(0) += term.primary.shift.mult() as usize;

                        if let Some(second) = term.second_use {
                            *sum_of.entry((reg, second.size, second.shift.right())).or_insert(0) += second.shift.mult() as usize;
                        }
                    }
                },
                Source::Dest(Dest::Mem(..)) => unreachable!(),
                Source::Imm(_) => todo!(),
                Source::Const {
                    value, ..
                } => {
                    let value = term.apply(value);
                    offset = offset.wrapping_add(value as i64);
                },
            }
        }

        MemAddr {
            sum_of,
            offset,
        }
    }

    pub fn smt<'ctx, S: SmtSolver<'ctx>>(&self, context: &mut S, storage: &mut StorageLocations<'ctx, X64Arch, S>) -> S::BV {
        let bv_offset = context.bv_from_i64(self.offset, 64);
        self.sum_of.iter().fold(bv_offset, |acc, (&(reg, size, shift), &mul)| {
            let val = storage
                .get(context, FilledLocation::Concrete(Location::Reg(reg)), &Sizes::default())
                .clone();
            assert_eq!(size, AddrTermSize::U64);

            let val = val.extract(63, 0);
            let val = if shift != 0 {
                val.bvashr(context.bv_from_u64(shift as u64, 64))
            } else {
                val
            };
            let val = if mul != 1 {
                val * context.bv_from_u64(mul.try_into().unwrap(), 64)
            } else {
                val
            };

            acc + val
        })
    }

    fn add_instr_size_if_rip(&mut self, byte_len: usize) {
        if self.sum_of.keys().any(|(reg, ..)| reg.is_pc()) {
            self.offset = self.offset.wrapping_add(byte_len as i64);
        }
    }
}

impl AddAssign for MemAddr {
    fn add_assign(&mut self, rhs: Self) {
        for (key, value) in rhs.sum_of.into_iter() {
            *self.sum_of.entry(key).or_insert(0) += value;
        }

        self.offset = self.offset.wrapping_add(rhs.offset);
    }
}

impl<'a> AddAssign<&'a MemAddr> for MemAddr {
    fn add_assign(&mut self, rhs: &'a MemAddr) {
        for (key, value) in rhs.sum_of.iter() {
            *self.sum_of.entry(*key).or_insert(0) += value;
        }

        self.offset = self.offset.wrapping_add(rhs.offset);
    }
}

struct Conv<'a, 'ctx, A: Arch, S: SmtSolver<'ctx>> {
    instance: &'a Dataflows<A, SynthesizedComputation>,
    storage: &'a mut StorageLocations<'ctx, A, S>,
    operands: &'a [(Operand, RegType)],
    undef_bvs: Vec<S::BV>,
    undef_bools: Vec<S::Bool>,
    mem_addrs: Vec<MemAddr>,
    z3_mem_addrs: Vec<(S::BV, u64)>,
    fix_rip: bool,
}

fn apply_sized_shift<'ctx, S: SmtSolver<'ctx>>(context: &mut S, s: AddrTermCalculation, bv: &S::BV) -> S::BV {
    let n = s.size.max_bit_influence() as u32;
    let bv = bv.clone().extract(n - 1, 0);
    let bv = if s.size.is_signed() {
        bv.sign_ext(64 - n)
    } else {
        bv.zero_ext(64 - n)
    };

    let bv = bv.bvashr(context.bv_from_u64(s.shift.right() as u64, 64));
    let bv = bv * context.bv_from_u64(s.shift.mult() as u64, 64);

    bv
}

fn apply_term<'ctx, S: SmtSolver<'ctx>>(context: &mut S, term: AddrTerm, bv: &S::BV) -> S::BV {
    let addr: S::BV = apply_sized_shift(context, term.primary, bv);

    if let Some(s) = term.second_use {
        addr + apply_sized_shift(context, s, bv)
    } else {
        addr
    }
}

impl<'a, 'ctx, S: SmtSolver<'ctx>> Conv<'a, 'ctx, X64Arch, S> {
    fn translate_addr_to_memory_index(&mut self, addr: &MemAddr) -> Option<usize> {
        trace!("Decoding address {addr:?}");

        let matches = self
            .mem_addrs
            .iter()
            .enumerate()
            .filter(|&(_, mem_addr)| {
                trace!("Comparing {mem_addr:?}");
                mem_addr == addr
            })
            .collect::<Vec<_>>();

        if matches.is_empty() {
            info!("No memory found for address {addr:?} in {:?}", self.mem_addrs);
            return None
        }

        trace!("Found applicable addresses: {matches:?}");

        assert_eq!(matches.len(), 1);

        Some(matches[0].0)
    }

    fn translate_z3node_to_memaddr(&mut self, node: &Z3Node) -> Option<&MemAddr> {
        if let Z3Node::Var(name) = node {
            let Some(n) = name.strip_prefix("addr") else {
                warn!("Unable to translate z3 node to memaddr: {node:?}");
                return None
            };
            let n = n.parse::<usize>().unwrap();
            let (Operand::Addr(addr), _) = &self.operands[n] else {
                todo!()
            };
            Some(addr)
        } else {
            None
        }
    }

    fn translate_z3node_to_mem_index(
        &mut self, context: &mut S, computation: &Z3Node, dasgupta_size: u64,
    ) -> Option<(usize, Size)> {
        if let Some(addr) = self.translate_z3node_to_memaddr(computation) {
            let mut mem_addr = addr.clone();
            mem_addr.add_instr_size_if_rip(self.instance.instr().byte_len());
            self.translate_addr_to_memory_index(&mem_addr)
                .map(|index| (index, Size::new(0, dasgupta_size as usize - 1)))
        } else {
            let z3 = computation.smt(context, self);
            let z3 = z3.as_bv().unwrap().simplify();

            trace!("Decoding address {z3:?}");

            if self.z3_mem_addrs.is_empty() {
                let prev_fix_rip = self.fix_rip;
                self.fix_rip = true;
                self.z3_mem_addrs = self
                    .instance
                    .addresses
                    .iter()
                    .map(|addr| {
                        let bv = addr
                            .calculation
                            .terms
                            .iter()
                            .zip(addr.inputs.iter())
                            .map(|(&term, source)| {
                                let val = Self::source_to_bv(context, self.instance, self.storage, source);
                                apply_term(context, term, &val)
                            })
                            .reduce(|a, b| a + b)
                            .unwrap()
                            + context.bv_from_i64(addr.calculation.offset, 64);
                        let bv = bv.simplify();

                        (bv, addr.size.end)
                    })
                    .collect();
                self.fix_rip = prev_fix_rip;
            }

            let matches = self
                .z3_mem_addrs
                .iter()
                .enumerate()
                .flat_map(|(index, (mem_addr, liblisa_size))| {
                    if let Some(n) = liblisa_size.checked_sub(dasgupta_size) {
                        for offset in 0..=n {
                            let check = (mem_addr.clone() + context.bv_from_u64(offset, 64).clone())
                                ._eq(z3.clone())
                                .not();
                            trace!("Comparing {mem_addr:?} + {offset} vs {z3:?}: {check:?}");

                            let result = context.check_assertions(&[check]);
                            trace!("Comparison result: {result:#?}");
                            match result {
                                SatResult::Unsat => return Some((index, offset)),
                                SatResult::Unknown => unreachable!(),
                                SatResult::Sat(model) => {
                                    trace!("Not equal when: {:?}", model);
                                },
                            }
                        }
                    }

                    None
                })
                .collect::<Vec<_>>();

            if !matches.is_empty() {
                trace!("Found applicable addresses: {matches:?}");
                assert_eq!(
                    matches.len(),
                    1,
                    "Found multiple applicable addresses for {z3:?}: {matches:?} in {}",
                    self.instance
                );

                let (index, offset) = matches[0];
                Some((index, Size::new(offset as usize, (offset + dasgupta_size - 1) as usize)))
            } else {
                debug!("No memory found for address {z3} in {:?}", self.z3_mem_addrs);
                None
            }
        }
    }

    fn source_to_bv(
        context: &mut S, _instance: &Dataflows<X64Arch, SynthesizedComputation>,
        storage: &mut StorageLocations<'ctx, X64Arch, S>, source: &Source<X64Arch>,
    ) -> S::BV {
        let val = match source {
            Source::Dest(Dest::Reg(reg, _)) if reg.is_zero() => context.bv_from_u64(0, 64),
            Source::Dest(dest) => {
                let val = storage.get(context, FilledLocation::Concrete(dest.into()), &Sizes::default());
                val
            },
            Source::Imm(_) => todo!(),
            Source::Const {
                value, ..
            } => context.bv_from_u64(*value, 64),
        };
        val
    }

    fn new(
        operands: &'a [(Operand, RegType)], storage: &'a mut StorageLocations<'ctx, X64Arch, S>,
        instance: &'a Dataflows<X64Arch, SynthesizedComputation>,
    ) -> Self {
        let mem_addrs = instance
            .addresses
            .iter()
            .map(|addr| {
                let offset = addr.calculation.offset;

                MemAddr::from_liblisa(offset, &addr.inputs, &addr.calculation.terms)
            })
            .collect();

        Conv {
            instance,
            storage,
            operands,
            undef_bools: Vec::new(),
            undef_bvs: Vec::new(),
            mem_addrs,
            z3_mem_addrs: Vec::new(),
            fix_rip: true,
        }
    }
}

impl<'a, 'ctx, S: SmtSolver<'ctx>> Kz3Converter<'ctx, S> for Conv<'a, 'ctx, X64Arch, S> {
    fn var(&mut self, context: &mut S, name: &str) -> Dynamic<'ctx, S> {
        let fixed_name = name.strip_prefix("reg_").unwrap_or(name);
        if let Some((reg, size)) = translate_variable_name_to_reg(fixed_name, self.operands) {
            if reg.is_zero() {
                trace!("Zero reg for: {fixed_name:?}");
                if fixed_name == "DF" {
                    context.bv_from_u64(0, 1).into_dynamic()
                } else {
                    context.bv_from_u64(0, size.num_bytes() as u32 * 8).into_dynamic()
                }
            } else {
                let bv = self
                    .storage
                    .get(context, FilledLocation::Concrete(Location::Reg(reg)), &Sizes::default());

                let bv = if reg.is_pc() && self.fix_rip {
                    bv + context.bv_from_u64(self.instance.instr().byte_len() as u64, reg.byte_size() as u32 * 8)
                } else {
                    bv
                };

                let bv = if size.start_byte != 0 || size.end_byte != reg.byte_size() - 1 {
                    trace!("{reg:?}.is_flags() == {}; fixed_name = {fixed_name:?}", reg.is_flags());
                    if reg.is_flags() && size.num_bytes() == 1 {
                        bv.extract(size.start_byte as u32 * 8, size.start_byte as u32 * 8)
                    } else {
                        bv.extract(size.end_byte as u32 * 8 + 7, size.start_byte as u32 * 8)
                    }
                } else {
                    bv
                };

                bv.into_dynamic()
            }
        } else if let Some(addr_index) = fixed_name.strip_prefix("addr") {
            let addr_index = addr_index.parse::<usize>().unwrap();
            let (op, _) = &self.operands[addr_index];
            let Operand::Addr(addr) = op else {
                panic!("Expected Operand::Addr for {fixed_name}: {op:?}");
            };

            let mut addr = addr.clone();
            addr.add_instr_size_if_rip(self.instance.instr().byte_len());
            addr.smt(context, self.storage).into_dynamic()
        } else {
            panic!("What is {fixed_name}?");
        }
    }

    fn mem(&mut self, context: &mut S, computation: &Z3Node, size: u32) -> Dynamic<'ctx, S> {
        assert!(size % 8 == 0);
        let Some((index, size)) = self.translate_z3node_to_mem_index(context, computation, size as u64 / 8) else {
            return context.new_bv_const("unknown_mem", size).into_dynamic()
        };
        trace!("memory: computation={computation:?}, size={size:?}; Index={index:?}");

        let bv = self
            .storage
            .get(context, FilledLocation::Concrete(Location::Memory(index)), &Sizes::default());

        trace!("memory {index:?} = {bv}");

        assert!(
            bv.get_size() >= size.end_byte as u32 * 8 + 8,
            "Memory access: {computation:?} should have size {size:?}, but it only has {} bits",
            bv.get_size()
        );

        bv.extract(size.end_byte as u32 * 8 + 7, size.start_byte as u32 * 8)
            .into_dynamic()
    }

    fn undef_bool(&mut self, context: &mut S) -> S::Bool {
        let undef = context.new_bool_const(format!("undef_bool{}", self.undef_bools.len()));
        self.undef_bools.push(undef.clone());
        undef
    }

    fn undef_bv(&mut self, context: &mut S, size: usize) -> S::BV {
        let undef = context.new_bv_const(format!("undef_bv{}", self.undef_bvs.len()), size.try_into().unwrap());
        self.undef_bvs.push(undef.clone());
        undef
    }

    fn imm(&mut self, context: &mut S, n: usize) -> S::BV {
        let (expr, _) = &self.operands[n];

        let Operand::Imm {
            val,
            size,
        } = expr
        else {
            panic!("Imm should be Z3Node::BvConst, not {expr:?}")
        };

        // Just crop the bits here, since there should be no immediate values that use more than 64 bits
        context.bv_from_u64(*val as u64, *size)
    }

    fn instruction_byte_length(&self) -> usize {
        self.instance.instr().byte_len()
    }
}

pub fn compare_semantics<'ctx, S: SmtSolver<'ctx>>(
    context: &mut S, instance: Encoding<X64Arch, SynthesizedComputation>, sd_semantics: &Kz3, asm: &str,
    operands: &[(Operand, RegType)],
) -> SemanticEquivalence {
    if instance.dataflows.output_dataflows().any(|o| o.computation.is_none()) {
        return SemanticEquivalence::LibLisaMissing
    }

    if sd_semantics.iter().any(|(_, s)| s.contains_unsupported()) {
        return SemanticEquivalence::Unsupported
    }

    debug!("Building Z3 model...");
    let mut storage = StorageLocations::new(context);
    let model = Z3Model::of(&instance, &mut storage, context);
    let concrete = model.compute_concrete_outputs(&instance, &mut storage, context);

    let mut concrete_outputs_missed = GrowingBitmap::new_all_ones(concrete.concrete_outputs().len());

    debug!(
        "Proving equivalence of storage locations {:?}...",
        sd_semantics.iter().map(|(v, _)| v).format(", ")
    );

    let mut instantiated_sd_semantics: HashMap<_, (Vec<StorageLocation>, Z3Node)> = HashMap::new();
    for (storage_loc, sd_expr) in sd_semantics.iter() {
        let mut conv = Conv::new(operands, &mut storage, &instance.dataflows);
        let loc = match storage_loc {
            StorageLocation::Reg(name) => {
                let Some((reg, size)) = translate_variable_name_to_reg(name, operands) else {
                    continue
                };

                Dest::Reg(reg, size)
            },
            StorageLocation::Mem {
                offset,
                size,
            } => {
                assert!(size % 8 == 0, "size must be a multiple of 8 for offset {offset:?}");
                let Some((index, size)) = conv.translate_z3node_to_mem_index(context, offset, *size as u64 / 8) else {
                    info!("memory access with address {offset:?} not found in {instance}");
                    continue
                };
                Dest::Mem(index, size)
            },
        };

        let val = if let Some((mut storage_locs, existing)) = instantiated_sd_semantics.remove(&loc) {
            storage_locs.push(storage_loc.clone());

            debug!("Multiple expressions for {loc:?}: {storage_locs:?}, substituting previous result into {sd_expr:?}");

            let substituted_expr = sd_expr.substitute_original_value(&existing);
            (storage_locs, substituted_expr)
        } else {
            (vec![storage_loc.clone()], sd_expr.clone())
        };

        instantiated_sd_semantics.insert(loc, val);
    }

    for (loc, (storage_locs, sd_expr)) in instantiated_sd_semantics.iter() {
        trace!("Checking {loc:?} = {sd_expr:?}");

        let mut conv = Conv::new(operands, &mut storage, &instance.dataflows);
        let sd_z3 = sd_expr.smt(context, &mut conv).as_bv().unwrap().zero_ext(128);
        // If a value is undefined, it may be any value.
        // So we need to check that there is no case where the value matches the output we found.
        // I.e.: forall val in values: dasgupta(val) != liblisa
        let undef = conv
            .undef_bools
            .iter()
            .map(|bv| bv.clone().into_dynamic())
            .chain(conv.undef_bvs.iter().map(|bv| bv.clone().into_dynamic()))
            .collect::<Vec<_>>();

        let mut missed_bytes = GrowingBitmap::new_all_ones(loc.size().num_bytes());
        for (co_index, o) in concrete.concrete_outputs().iter().enumerate() {
            if loc.overlaps(&o.target()) {
                let liblisa_size = o.target().size();
                let Some(area) = liblisa_size.overlapping_area(loc.size()) else {
                    continue
                };

                if area != liblisa_size {
                    println!("TODO: Areas not completely overlapping");
                }

                let range = area.start_byte - loc.size().start_byte..area.end_byte + 1 - loc.size().start_byte;
                trace!("Marking bytes {range:?} as covered");
                missed_bytes.clear_range(range);
                concrete_outputs_missed.reset(co_index);

                // `o.smt()` is always Some if the output has a computation, which we check at the start of this function.
                let liblisa_expr = o.smt().unwrap();

                trace!("Comparing {loc:?} vs {:?}; SD={sd_expr:?}", o.target());
                // println!("Compare {:?} vs {sd_expr:?}", liblisa_expr.simplify());

                let mut assertions = Vec::new();
                for &index in concrete.intermediate_values_needed() {
                    let imm = &model.intermediate_outputs()[index];
                    let name = &imm.name();
                    let smt = imm.smt().unwrap();

                    assert_eq!(name.get_size(), smt.get_size(), "{name} = {smt}");

                    let condition = (*name).clone()._eq(smt.clone());
                    assertions.push(condition);
                }

                trace!("Area: {area:?}, loc: {loc:?}, size: {liblisa_size:?}");
                let loc_full_size = match o.target() {
                    Dest::Reg(reg, _) => reg.byte_size(),
                    Dest::Mem(index, _) => instance.dataflows.addresses[index].size.end as usize,
                };
                let sd_z3 = match o.target().value_type() {
                    ValueType::Num => sd_z3.clone(),
                    // TODO: What if loc is not full register?
                    ValueType::Bytes(_) => sd_z3.clone().swap_bytes(loc_full_size),
                };
                let (sd_lo, sd_hi) = (
                    (area.start_byte - loc.size().start_byte),
                    (area.end_byte - loc.size().start_byte),
                );
                let (sd_lo, sd_hi) = match o.target().value_type() {
                    ValueType::Num => (sd_lo, sd_hi),
                    ValueType::Bytes(_) => (loc_full_size - sd_hi - 1, loc_full_size - sd_lo - 1),
                };
                trace!("Actually extracting: {sd_hi}..{sd_lo} after byte swap");
                let sd_z3 = sd_z3.extract(sd_hi as u32 * 8 + 7, sd_lo as u32 * 8);
                let liblisa_expr = liblisa_expr.clone().extract(
                    (area.end_byte - liblisa_size.start_byte) as u32 * 8 + 7,
                    (area.start_byte - liblisa_size.start_byte) as u32 * 8,
                );
                let check = liblisa_expr.clone()._eq(sd_z3.clone()).not();
                let check = if undef.is_empty() {
                    check
                } else {
                    context.forall_const(&undef, check)
                };

                let result = if asm.starts_with("vmpsadbw") {
                    // Perform byte-wise comparison
                    check_bytewise(area, &liblisa_expr, &sd_z3, &assertions, context)
                } else {
                    assertions.push(check.clone());
                    trace!(
                        "Checking assertions:\n {:?}",
                        assertions.iter().map(|x| x.clone().simplify()).format("\n")
                    );
                    context.check_assertions(&assertions)
                };

                trace!("Result: {result:?}");
                match result {
                    SatResult::Unsat => {},
                    SatResult::Unknown => {
                        debug!("Checking {loc:?}={sd_expr:?} timed out; Check: {:?}", check.simplify());
                        println!("\nTimed out: {:?} vs {loc:?}={sd_expr:?} in {asm} & {instance}", o.target());
                        return SemanticEquivalence::Timeout
                    },
                    SatResult::Sat(_) => {
                        drop(result);
                        assertions.push(
                            context
                                .new_bv_const("liblisa_result", liblisa_expr.get_size())
                                ._eq(liblisa_expr.clone()),
                        );
                        assertions.push(context.new_bv_const("dasgupta_result", sd_z3.get_size())._eq(sd_z3.clone()));
                        let new = match context.check_assertions(&assertions) {
                            SatResult::Sat(model) => Some(model),
                            _ => None,
                        };

                        println!(
                            "\nSemantics not equal: {:?} vs {loc:?}={sd_expr:?} in asm {asm} & {instance}\n\n{new:?}",
                            o.target()
                        );
                        debug!("SMT check: {:?}", check.simplify());
                        debug!("libLISA semantics: {:?}", liblisa_expr.simplify());
                        debug!("Dasgupta semantics: {:?}", sd_z3.simplify());
                        return SemanticEquivalence::NotEqual
                    },
                }
            }
        }

        // Ensure that the bytes we missed are the identity function
        trace!("Checking identity");
        if storage_locs.iter().any(|storage_loc| !sd_expr.is_identity(storage_loc)) {
            trace!(
                "Missed bytes {:?} for storage location {storage_locs:?} / {loc:?}",
                missed_bytes.iter_one_indices().format(", ")
            );
            for byte_index in missed_bytes.iter_one_indices() {
                let original_byte_index = loc.size().start_byte + byte_index;
                let original: S::BV = storage.get(context, FilledLocation::Concrete(loc.into()), &Sizes::default());
                let original = original.extract(original_byte_index as u32 * 8 + 7, original_byte_index as u32 * 8);
                let new = sd_z3.clone().extract(byte_index as u32 * 8 + 7, byte_index as u32 * 8);

                let check = original._eq(new).not();
                let check = if undef.is_empty() {
                    check
                } else {
                    context.forall_const(&undef, check)
                };

                match context.check_assertions(&[check]) {
                    SatResult::Unsat => (),
                    SatResult::Unknown => {
                        println!(
                            "\nEquivalence unknown: Byte {byte_index} in {loc:?} is not identity in asm {asm} vs {instance}"
                        );
                        debug!("Byte {byte_index} in {loc:?} is not identity!");
                        return SemanticEquivalence::Timeout
                    },
                    SatResult::Sat(model) => {
                        println!(
                            "\nSemantics not equal: Byte {byte_index} in {loc:?} is not identity in asm {asm} vs {instance}\n\n{model:?}"
                        );
                        debug!("Byte {byte_index} in {loc:?} is not identity!");
                        return SemanticEquivalence::NotEqual
                    },
                }
            }
        }
    }

    // Ensure that the concrete outputs we have missed are the identity function
    debug!("Checking identity of concrete outputs...");
    for index in concrete_outputs_missed.iter_one_indices() {
        let o = &concrete.concrete_outputs()[index];
        if matches!(o.target(), Dest::Reg(r, _) if r.is_pc()) {
            continue
        }

        let mut assertions = Vec::new();

        // `o.smt()` is always Some if the output has a computation, which we check at the start of this function.
        let liblisa_expr = o.smt().unwrap();
        for &index in concrete.intermediate_values_needed() {
            let imm = &model.intermediate_outputs()[index];
            let condition = imm.name().clone()._eq(imm.smt().unwrap().clone());
            assertions.push(condition);
        }

        let original = storage.get(context, FilledLocation::Concrete(o.target().into()), &Sizes::default());
        let size = o.target().size();
        let original = original.extract(size.end_byte as u32 * 8 + 7, size.start_byte as u32 * 8);

        assertions.push(liblisa_expr.clone()._eq(original).not());
        match context.check_assertions(&assertions) {
            SatResult::Unsat => (),
            SatResult::Unknown => {
                println!(
                    "\nEquivalence unknown: concrete output #{index} {o:?} was missed, and it is not identity in asm {asm} & {instance}\n\nAvailable: {:?}",
                    sd_semantics.iter().map(|(loc, _)| loc).format(", ")
                );
                debug!("Concrete output #{index} {o:?}liblisa_expr._eq(&original).not() was missed, and it is not identity");
                return SemanticEquivalence::Timeout
            },
            SatResult::Sat(model) => {
                println!(
                    "\nSemantics not equal: concrete output #{index} {o:?} was missed, and it is not identity in asm {asm} & {instance}\n\n{model:?}\n\nAvailable: {:?}",
                    sd_semantics.iter().map(|(loc, _)| loc).format(", ")
                );
                debug!("Concrete output #{index} {o:?} was missed, and it is not identity");
                return SemanticEquivalence::NotEqual
            },
        }
    }

    SemanticEquivalence::Equal
}

fn check_bytewise<'a, 'ctx, S: SmtSolver<'ctx>>(
    area: Size, liblisa_expr: &S::BV, sd_z3: &S::BV, assertions: &[S::Bool], context: &'a mut S,
) -> SatResult<S::ModelRef<'a>> {
    debug!("Performing full bytewise comparison for vmpsadbw");
    for b in 0..area.num_bytes() as u32 {
        debug!("Expression sizes: {} vs {}", liblisa_expr.get_size(), sd_z3.get_size());
        let check = liblisa_expr
            .clone()
            .extract(b * 8 + 7, b * 8)
            ._eq(sd_z3.clone().extract(b * 8 + 7, b * 8))
            .not()
            .simplify();
        debug!("Checking byte {b} => {check}");
        let mut assertions = assertions.to_vec();
        assertions.push(check);
        let r = context.check_assertions(&assertions);
        debug!("Result for byte {b}: {r:?}");
        match r {
            SatResult::Unsat => (),
            _ => {
                panic!("Bytewise compare failed ({r:?}) and lifetimes don't allow me to return the model")
            },
        }
    }

    SatResult::Unsat
}

pub fn split_operands(operands: &str) -> Vec<&str> {
    let mut result = Vec::new();
    let mut remaining = operands;
    loop {
        let next_parens = remaining.find('(');
        if let Some(next_comma) = remaining.find(',') {
            if next_parens.map(|next_parens| next_parens < next_comma).unwrap_or(false) {
                let closing_parens = remaining.find(')').unwrap();
                let next_comma = remaining[closing_parens..].find(',');
                result.push(&remaining[..closing_parens + 1]);
                remaining = &remaining[next_comma.map(|next| closing_parens + next + 1).unwrap_or(remaining.len())..];
            } else {
                result.push(&remaining[..next_comma]);
                remaining = &remaining[next_comma + 1..];
            }
        } else {
            result.push(remaining);
            break
        }
    }

    for s in result.iter_mut() {
        *s = s.trim();
    }

    result.retain(|s| !s.is_empty());

    result
}
