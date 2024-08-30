use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{BufReader, BufWriter, Write};
use std::path::PathBuf;
use std::process::Stdio;
use std::sync::atomic::AtomicUsize;
use std::sync::Mutex;
use std::time::Duration;

use clap::Parser;
use compare::MemAddr;
use itertools::Itertools;
use kparser::ast::{parse, Declaration, Expr, Statement};
use kparser::rewrite::{ListKind, TokenTree};
use kparser::z3::Kz3;
use liblisa::arch::x64::{PrefixScope, X64Arch};
use liblisa::arch::{Register, Scope};
use liblisa::encoding::dataflows::AddrTermSize;
use liblisa::encoding::Encoding;
use liblisa::semantics::default::computation::SynthesizedComputation;
use liblisa::smt::z3::Z3Solver;
use liblisa::smt::{CacheHitCounter, CachedSolver, FileCache, SharedCache};
use liblisa::Instruction;
use liblisa_progress::{progress_data, Progress, ProgressUsize};
use libopcodes_rs::Disassembler;
use log::{debug, info, trace, warn};
use rand::seq::SliceRandom;
use rayon::iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator};
use serde::{Deserialize, Serialize};
use z3::{Config, Context};

use crate::compare::{alias_to_full_reg, compare_semantics, split_operands, translate_variable_name_to_reg};
use crate::disasm::libopcodes_disassemble;
use crate::instrs::{extract_instrs, fix_instr, ExtractedInstrs};

pub mod compare;
pub mod disasm;
pub mod instrs;

#[derive(clap::Parser)]
enum Args {
    ExtractInstrs {
        semantics: PathBuf,

        #[clap(long)]
        output: PathBuf,
    },
    CheckDisasm {
        instr: Instruction,
    },
    ExtractDasgupta {
        k_semantics: PathBuf,

        #[clap(long)]
        output: PathBuf,
    },
    CompareDasgupta {
        #[clap(long)]
        instrs: PathBuf,

        #[clap(long)]
        semantics: PathBuf,

        #[clap(long)]
        dasgupta_semantics: PathBuf,

        #[clap(long)]
        output: Option<PathBuf>,

        #[clap(long)]
        solver_cache: PathBuf,

        #[clap(long)]
        filter_asm_prefix: Vec<String>,

        #[clap(long)]
        filter_asm: Vec<String>,
    },
    GenerateTable {
        comparison: PathBuf,

        #[clap(long)]
        instrs: PathBuf,

        #[clap(long)]
        debug: bool,

        #[clap(long)]
        semantics: PathBuf,

        #[clap(long)]
        k_semantics: PathBuf,

        #[clap(long)]
        dasgupta_semantics: PathBuf,

        #[clap(long)]
        latex: bool,
    },
}

#[derive(Serialize, Deserialize)]
struct ComparisonResult {
    instrs: HashSet<(bool, Instruction)>,
    asm: String,

    mnemonic: String,
    operand_types: Vec<RegType>,

    comparison_result: SemanticEquivalence,

    #[serde(default)]
    dasgupta_path: Option<PathBuf>,
}

#[derive(Serialize, Deserialize, Debug)]
struct DasguptaSemantic {
    file: PathBuf,
    mnemonic: String,
    operand_types: Vec<RegType>,
    semantics: Option<Kz3>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum RegType {
    Rh,
    R8,
    R16,
    R32,
    R64,
    Xmm,
    Ymm,
    Imm,
    Imm8,
    Imm16,
    Imm32,
    Imm64,

    Cl,
    Al,
    Ax,
    Eax,
    Rax,
    Xmm0,

    X86Id,
    MemOffset,
    Hex { val: u64, num_bytes: Option<usize> },

    Mm0,
    Mm,
}
impl RegType {
    fn from_str(op: &str) -> RegType {
        match op {
            "%al" => RegType::Al,
            "%ah" => RegType::Rh,
            "%ax" => RegType::Ax,
            "%eax" => RegType::Eax,
            "%rax" => RegType::Rax,

            "%bl" => RegType::R8,
            "%bh" => RegType::Rh,
            "%bx" => RegType::R16,
            "%ebx" => RegType::R32,
            "%rbx" => RegType::R64,

            "%cl" => RegType::Cl,
            "%ch" => RegType::Rh,
            "%cx" => RegType::R16,
            "%ecx" => RegType::R32,
            "%rcx" => RegType::R64,

            "%dl" => RegType::R8,
            "%dh" => RegType::Rh,
            "%dx" => RegType::R16,
            "%edx" => RegType::R32,
            "%rdx" => RegType::R64,

            "%sil" => RegType::R8,
            "%si" => RegType::R16,
            "%esi" => RegType::R32,
            "%rsi" => RegType::R64,

            "%dil" => RegType::R8,
            "%di" => RegType::R16,
            "%edi" => RegType::R32,
            "%rdi" => RegType::R64,

            "%spl" => RegType::R8,
            "%sp" => RegType::R16,
            "%esp" => RegType::R32,
            "%rsp" => RegType::R64,

            "%bpl" => RegType::R8,
            "%bp" => RegType::R16,
            "%ebp" => RegType::R32,
            "%rbp" => RegType::R64,

            "%r8b" => RegType::R8,
            "%r8w" => RegType::R16,
            "%r8d" => RegType::R32,
            "%r8" => RegType::R64,

            "%r9b" => RegType::R8,
            "%r9w" => RegType::R16,
            "%r9d" => RegType::R32,
            "%r9" => RegType::R64,

            "%r10b" => RegType::R8,
            "%r10w" => RegType::R16,
            "%r10d" => RegType::R32,
            "%r10" => RegType::R64,

            "%r11b" => RegType::R8,
            "%r11w" => RegType::R16,
            "%r11d" => RegType::R32,
            "%r11" => RegType::R64,

            "%r12b" => RegType::R8,
            "%r12w" => RegType::R16,
            "%r12d" => RegType::R32,
            "%r12" => RegType::R64,

            "%r13b" => RegType::R8,
            "%r13w" => RegType::R16,
            "%r13d" => RegType::R32,
            "%r13" => RegType::R64,

            "%r14b" => RegType::R8,
            "%r14w" => RegType::R16,
            "%r14d" => RegType::R32,
            "%r14" => RegType::R64,

            "%r15b" => RegType::R8,
            "%r15w" => RegType::R16,
            "%r15d" => RegType::R32,
            "%r15" => RegType::R64,

            "%xmm0" => RegType::Xmm0,
            "%xmm1" => RegType::Xmm,
            "%xmm2" => RegType::Xmm,
            "%xmm3" => RegType::Xmm,
            "%xmm4" => RegType::Xmm,
            "%xmm5" => RegType::Xmm,
            "%xmm6" => RegType::Xmm,
            "%xmm7" => RegType::Xmm,
            "%xmm8" => RegType::Xmm,
            "%xmm9" => RegType::Xmm,
            "%xmm10" => RegType::Xmm,
            "%xmm11" => RegType::Xmm,
            "%xmm12" => RegType::Xmm,
            "%xmm13" => RegType::Xmm,
            "%xmm14" => RegType::Xmm,
            "%xmm15" => RegType::Xmm,

            "%ymm0" => RegType::Ymm,
            "%ymm1" => RegType::Ymm,
            "%ymm2" => RegType::Ymm,
            "%ymm3" => RegType::Ymm,
            "%ymm4" => RegType::Ymm,
            "%ymm5" => RegType::Ymm,
            "%ymm6" => RegType::Ymm,
            "%ymm7" => RegType::Ymm,
            "%ymm8" => RegType::Ymm,
            "%ymm9" => RegType::Ymm,
            "%ymm10" => RegType::Ymm,
            "%ymm11" => RegType::Ymm,
            "%ymm12" => RegType::Ymm,
            "%ymm13" => RegType::Ymm,
            "%ymm14" => RegType::Ymm,
            "%ymm15" => RegType::Ymm,

            "%mm0" => RegType::Mm0,
            "%mm1" => RegType::Mm,
            "%mm2" => RegType::Mm,
            "%mm3" => RegType::Mm,
            "%mm4" => RegType::Mm,
            "%mm5" => RegType::Mm,
            "%mm6" => RegType::Mm,
            "%mm7" => RegType::Mm,
            "%mm8" => RegType::Mm,
            "%mm9" => RegType::Mm,
            "%mm10" => RegType::Mm,
            "%mm11" => RegType::Mm,
            "%mm12" => RegType::Mm,
            "%mm13" => RegType::Mm,
            "%mm14" => RegType::Mm,
            "%mm15" => RegType::Mm,
            _ => unimplemented!("RegType::from_str({op})"),
        }
    }

    fn guess_val_size(val: u64) -> u32 {
        64 - val.leading_zeros().max(val.leading_ones())
    }

    pub fn guess_val_size_i128(val: i128) -> u32 {
        128 - val.leading_zeros().max(val.leading_ones())
    }

    fn matches(&self, real_type: &RegType) -> bool {
        match (self, real_type) {
            (a, b) if a == b => true,
            (
                RegType::Hex {
                    val: a, ..
                },
                RegType::Hex {
                    val: b, ..
                },
            ) => a == b,
            (RegType::R8, RegType::Al | RegType::Cl) 
            | (RegType::R16, RegType::Ax) 
            | (RegType::R32, RegType::Eax) 
            | (RegType::R64, RegType::Rax) 
            | (RegType::Xmm, RegType::Xmm0) => true,
            (
                RegType::Imm,
                RegType::Hex {
                    ..
                },
            ) => true,
            (
                RegType::Imm8,
                RegType::Hex {
                    val,
                    num_bytes,
                },
            ) => Self::guess_val_size(*val) <= 8,
            (
                RegType::Imm16,
                RegType::Hex {
                    val,
                    num_bytes,
                },
            ) => Self::guess_val_size(*val) <= 16,
            (
                RegType::Imm32,
                RegType::Hex {
                    val,
                    num_bytes,
                },
            ) => Self::guess_val_size(*val) <= 32,
            (
                RegType::Imm64,
                RegType::Hex {
                    ..
                },
            ) => true,
            _ => false,
        }
    }

    fn match_score(&self, real_type: &RegType) -> usize {
        match (self, real_type) {
            (
                RegType::Hex {
                    val: a, ..
                },
                RegType::Hex {
                    val: b, ..
                },
            ) if a == b => 15,
            (
                RegType::Imm8,
                RegType::Hex {
                    val,
                    num_bytes,
                },
            ) if Self::guess_val_size(*val) < 8 => 13,
            (
                RegType::Imm16,
                RegType::Hex {
                    val,
                    num_bytes,
                },
            ) if Self::guess_val_size(*val) < 16 => {
                if Self::guess_val_size(*val) >= 8 {
                    12
                } else {
                    5
                }
            },
            (
                RegType::Imm32,
                RegType::Hex {
                    val,
                    num_bytes,
                },
            ) if Self::guess_val_size(*val) < 32 => {
                if Self::guess_val_size(*val) >= 16 {
                    11
                } else {
                    4
                }
            },
            (
                RegType::Imm64,
                RegType::Hex {
                    ..
                },
            ) => 10,
            (a, b) if a == b => 10,
            (a, b) if a.matches(b) => 1,
            _ => 0,
        }
    }

    fn anonymize(&self) -> RegType {
        match self {
            RegType::Hex {
                val,
                num_bytes,
            } if Self::guess_val_size(*val) < 8 => RegType::Imm8,
            RegType::Hex {
                val,
                num_bytes,
            } if Self::guess_val_size(*val) < 16 => RegType::Imm16,
            RegType::Hex {
                val,
                num_bytes,
            } if Self::guess_val_size(*val) < 32 => RegType::Imm32,
            RegType::Hex {
                ..
            } => RegType::Imm64,
            other => *other,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Operand {
    Var(String),
    Addr(MemAddr),
    Imm { val: i128, size: u32 },
}

thread_local! {
    static CONTEXT: Context = {
        let mut config = Config::new();
        config.set_timeout_msec(30_000);
        Context::new(&config)
    }
}

fn main() {
    env_logger::init();
    let args = Args::parse();
    match args {
        Args::ExtractInstrs {
            semantics,
            output,
        } => {
            let semantics: Vec<Encoding<X64Arch, SynthesizedComputation>> =
                serde_json::from_reader(BufReader::new(File::open(semantics).unwrap())).unwrap();
            let instrs = extract_instrs(&semantics);
            println!("Generated {} instructions", instrs.len());

            serde_json::to_writer(
                BufWriter::new(File::create(output).unwrap()),
                &ExtractedInstrs {
                    num_encodings: semantics.len(),
                    instrs: instrs.into_iter().collect(),
                },
            )
            .unwrap();
        },
        Args::ExtractDasgupta {
            k_semantics,
            output,
        } => {
            let files = find_dasgupta_semantics_files(k_semantics);

            println!("Files: {}", files.len());

            let patches = [
                // Complex syntax that we don't want to implement
                (
                    r#"... "RIP" |-> ( PC => MemVal)  ..."#,
                    r#"RSMap:Map => updateMap(RSMap, "RIP" |-> MemVal)"#,
                ),
                // Will select incorrect rule because of missing typing
                (r#"execinstr (shldl R, MIdest:MInt"#, r#"execinstr (shldl R:R32, MIdest:MInt"#),
                (r#"execinstr (shrdl R, MIdest:MInt"#, r#"execinstr (shrdl R:R32, MIdest:MInt"#),
                // We need bitvector sizes for undefined MInts
                (
                    r#"convToRegKeys(R) |-> (undefMInt)"#,
                    r#"convToRegKeys(R) |-> (createUndefMInt(bitwidthMInt(getParentValue(R, RSMap))))"#,
                ),
                (
                    r#"convToRegKeys(R2) |-> (undefMInt)"#,
                    r#"convToRegKeys(R2) |-> (createUndefMInt(bitwidthMInt(getParentValue(R2, RSMap))))"#,
                ),
                // Our operator precedence differs for these expressions.
                (
                    r#"notBool eqMInt({RSMap["ZF"]}:>MInt, mi(1, 0)) "#,
                    r#"(notBool eqMInt({RSMap["ZF"]}:>MInt, mi(1, 0)))"#,
                ),
                (
                    r#"notBool eqMInt({RSMap["CF"]}:>MInt, mi(1, 0)) "#,
                    r#"(notBool eqMInt({RSMap["CF"]}:>MInt, mi(1, 0)))"#,
                ),
                (
                    r#"notBool eqMInt(Count, mi(bitwidthMInt(Count), 0))"#,
                    r#"(notBool eqMInt(Count, mi(bitwidthMInt(Count), 0)))"#,
                ),
            ];

            let parsed_files = files
                .iter()
                .flat_map(|file| {
                    let mut content = std::fs::read_to_string(file).unwrap();
                    for (from, to) in patches {
                        content = content.replace(from, to);
                    }

                    match parse(&content) {
                        Ok(d) => Some((file, d)),
                        Err(e) => {
                            println!("Failed to parse {file:?}: {e}");
                            None
                        },
                    }
                })
                .collect::<Vec<_>>();

            println!("Parsed all files");

            let rules = parsed_files
                .iter()
                .flat_map(|(file, decls)| {
                    decls
                        .iter()
                        .flat_map(|decl| match decl {
                            Declaration::Requires(_) => [].iter(),
                            Declaration::Module {
                                body, ..
                            } => body.iter(),
                        })
                        .flat_map(|stmt| match stmt {
                            Statement::Rule(rule) => Some(rule),
                            _ => None,
                        })
                        .flat_map(|rule| rule.cells.iter())
                        .filter(|cell| cell.name.as_str() == "k")
                        .map(|cell| &cell.rewrite.from)
                        .map(move |expr| (expr, (file, decls)))
                })
                .flat_map(|(expr, decls)| match expr {
                    Expr::ExecInstr {
                        instr,
                        operands,
                    } => {
                        let Expr::Var(opcode) = instr.untyped() else {
                            panic!("Unable to extract opcode from {instr:?}")
                        };
                        let opcode = opcode.as_str();

                        let operands = match &**operands {
                            Expr::List(operands) => operands.as_slice(),
                            Expr::ListNil(_) => &[],
                            _ => panic!("Operands not a list: {operands:?}"),
                        };

                        let mut valid = true;
                        let operand_types = operands
                            .iter()
                            .flat_map(|operand| match operand {
                                Expr::ListNil(_) => None,
                                Expr::Typed {
                                    ty,
                                    expr,
                                } => Some(match ty.as_str() {
                                    "Rh" => RegType::Rh,
                                    "R8" => RegType::R8,
                                    "R16" => RegType::R16,
                                    "R32" => RegType::R32,
                                    "R64" => RegType::R64,
                                    "Xmm" => RegType::Xmm,
                                    "Ymm" => RegType::Ymm,
                                    "Imm" => {
                                        let Expr::Var(v) = &**expr else { panic!() };
                                        match v.as_str() {
                                            "Imm8" => RegType::Imm8,
                                            "Imm16" => RegType::Imm16,
                                            "Imm32" => RegType::Imm32,
                                            "Imm64" => RegType::Imm64,
                                            v => {
                                                warn!("Unknown imm size: {v}");
                                                RegType::Imm
                                            },
                                        }
                                    },
                                    "Mem" | "MemOffset" => RegType::MemOffset,
                                    other => {
                                        debug!("ignoring operand type: {other} in {opcode} {operands:?}");
                                        valid = false;
                                        return None
                                    },
                                }),
                                Expr::Var(name) => {
                                    println!("ignoring variable {name:?} in {opcode} {operands:?}");
                                    valid = false;
                                    None
                                },
                                Expr::Fun {
                                    name,
                                    args,
                                } if name.as_str() == "memOffset" => {
                                    assert_eq!(args.len(), 1);
                                    Some(RegType::MemOffset)
                                },
                                Expr::Compose(c) => {
                                    if let [Expr::Dollarydoo, Expr::Hex(num)] = c.as_slice() {
                                        Some(RegType::Hex {
                                            val: (*num).try_into().unwrap(),
                                            num_bytes: None,
                                        })
                                    } else {
                                        None
                                    }
                                },
                                Expr::String(s) => Some(match s.as_str() {
                                    "%rax" => RegType::Rax,
                                    "%eax" => RegType::Eax,
                                    "%ax" => RegType::Ax,
                                    "%al" => RegType::Al,
                                    "%cl" => RegType::Cl,
                                    "%xmm0" => RegType::Xmm0,
                                    _ => unimplemented!("fixed operand {s}"),
                                }),
                                _ => panic!("Unable to handle operand: {operand:?} in {opcode} {operands:?}"),
                            })
                            .collect::<Vec<_>>();

                        if valid {
                            Some((opcode, operand_types, decls))
                        } else {
                            println!("ERR: invalid specification: {opcode} {operands:?}");
                            None
                        }
                    },
                    // TODO: We aren't parsing execinstr(rep.. cmpsq, ...) correctly
                    other => {
                        println!("ERR: Unable to extract execinstr: {other:?}");
                        None
                    },
                })
                .collect::<Vec<_>>();

            println!("{} rules", rules.len());

            let results = Progress::run(
                progress_data! {
                    P {
                        num_ok: ProgressUsize = 0,
                        num_processed: ProgressUsize = 0,
                        total: usize = rules.len(),
                        pending: Mutex<HashSet<String>> = Mutex::new(HashSet::new()),
                    }, |f, P { num_ok, num_processed, total, pending }| {
                        write!(f, "Computing semantics: {num_processed} / {total} processed, {num_ok} / {num_processed} converted OK")?;

                        let pending = pending.lock().unwrap();
                        if pending.len() <= 5 {
                            write!(f, " -- {}", pending.iter().format(", "))?;
                        }

                        Ok(())
                    }
                },
                |p| {
                    rules
                        .par_iter()
                        .with_max_len(1)
                        .map(|(opcode, operand_types, (file, decls))| {
                            let _d = p.num_processed.delayed_increment();

                            println!("\nProcessing opcode: {opcode} {operand_types:?}");
                            p.pending.lock().unwrap().insert(format!("{opcode} {operand_types:?}"));
                            let op = TokenTree::String(opcode.to_string());
                            let operands = operand_types
                                .iter()
                                .enumerate()
                                .map(|(n, op)| match op {
                                    RegType::Al => TokenTree::String(String::from("%al")),
                                    RegType::Ax => TokenTree::String(String::from("%ax")),
                                    RegType::Eax => TokenTree::String(String::from("%eax")),
                                    RegType::Rax => TokenTree::String(String::from("%rax")),
                                    RegType::Xmm0 => TokenTree::String(String::from("%xmm0")),
                                    RegType::Cl => TokenTree::String(String::from("%cl")),
                                    RegType::Hex {
                                        val, ..
                                    } => TokenTree::List {
                                        kind: ListKind::Compose,
                                        head: Box::new(TokenTree::Dollarydoo),
                                        tail: Box::new(TokenTree::List {
                                            kind: ListKind::Compose,
                                            head: Box::new(TokenTree::Hex(*val as u128)),
                                            tail: Box::new(TokenTree::Nil),
                                        }),
                                    },
                                    RegType::X86Id => todo!(),
                                    RegType::MemOffset => TokenTree::Fun {
                                        name: String::from("memOffset"),
                                        args: vec![TokenTree::String(format!("%virt:{op:?}:{n}"))],
                                    },
                                    RegType::Imm | RegType::Imm8 | RegType::Imm16 | RegType::Imm32 | RegType::Imm64 => {
                                        TokenTree::List {
                                            kind: ListKind::Compose,
                                            head: Box::new(TokenTree::Dollarydoo),
                                            tail: Box::new(TokenTree::List {
                                                kind: ListKind::Compose,
                                                head: Box::new(TokenTree::String(format!("%virt:Imm:{n}"))),
                                                tail: Box::new(TokenTree::Nil),
                                            }),
                                        }
                                    },
                                    RegType::Rh
                                    | RegType::R8
                                    | RegType::R16
                                    | RegType::R32
                                    | RegType::R64
                                    | RegType::Xmm
                                    | RegType::Ymm => TokenTree::String(format!("%virt:{op:?}:{n}")),
                                    RegType::Mm | RegType::Mm0 => unreachable!(),
                                })
                                .collect::<Vec<_>>();

                            // These use requirements to restrict which execinstrs apply
                            // We didn't implement that so for us it's just an infinite loop
                            let skip = ["vmaskmovdqu", "maskmovdqu"].contains(opcode);

                            let result = if skip {
                                println!("\nSkipping {opcode} (in skip list) with {operands:?}");
                                None
                            } else {
                                Kz3::expand(decls, &op, &operands)
                            };

                            println!("\n{opcode} {operands:?} = {result:?}");

                            if result.is_some() {
                                p.num_ok.increment();
                            }

                            p.pending.lock().unwrap().remove(&format!("{opcode} {operand_types:?}"));

                            DasguptaSemantic {
                                file: (**file).clone(),
                                mnemonic: opcode.to_string(),
                                operand_types: operand_types.clone(),
                                semantics: result,
                            }
                        })
                        .collect::<Vec<_>>()
                },
            );

            serde_json::to_writer(BufWriter::new(File::create(output).unwrap()), &results).unwrap();
        },
        Args::CompareDasgupta {
            instrs,
            semantics,
            dasgupta_semantics,
            output,
            solver_cache,
            filter_asm_prefix,
            filter_asm,
        } => {
            let ExtractedInstrs {
                num_encodings,
                instrs,
            } = serde_json::from_reader(BufReader::new(File::open(instrs).unwrap())).unwrap();

            let solver_cache = FileCache::new(&solver_cache);
            let solver_cache = CacheHitCounter::new(solver_cache);
            let num_misses = solver_cache.num_misses();
            let num_hits = solver_cache.num_hits();
            let solver_cache = SharedCache::new(solver_cache);

            let liblisa_semantics: Vec<Encoding<X64Arch, SynthesizedComputation>> =
                serde_json::from_reader(BufReader::new(File::open(semantics).unwrap())).unwrap();

            let mut deserializer = serde_json::Deserializer::from_reader(File::open(dasgupta_semantics).unwrap());
            deserializer.disable_recursion_limit();
            let flat_dasgupta_semantics = Vec::<DasguptaSemantic>::deserialize(&mut deserializer).unwrap();
            let dasgupta_semantics = {
                let mut m = HashMap::new();
                for s in flat_dasgupta_semantics.iter() {
                    let file = s.file.as_os_str().to_str().unwrap();
                    if file.contains("systemInstructions/jrcxz_rel32.k")
                        || file.contains("systemInstructions/jecxz_rel32.k") {
                        // These are incorrectly specified.
                        // The disassembler is adding the instruction length to the offset, which makes it impossible to detect immediate sizes properly.
                        // For example, jrcxz 0x7E gets disassembled to jrcxz 0x80...
                        // (this would probably break Dasgupta's semantics as well, but right now we only need to make sure our tool picks the right semantics to match against)
                        continue
                    }

                    m.entry(s.mnemonic.clone()).or_insert_with(Vec::new).push(s);
                }

                m
            };

            let instr_to_encoding = {
                let mut map = HashMap::new();
                for ((_, instr), indices) in instrs.iter() {
                    map.entry(*instr).or_insert_with(Vec::new).extend(indices.iter().copied());
                }

                map
            };
            let mapping = libopcodes_disassemble(num_encodings, instrs);

            let mut mapping = mapping.iter().collect::<Vec<_>>();
            mapping.sort_by_key(|(asm, _)| *asm);
            mapping.shuffle(&mut rand::thread_rng());

            if !filter_asm_prefix.is_empty() {
                mapping.retain(|(asm, _)| filter_asm_prefix.iter().any(|filter| asm.starts_with(filter)));
            }

            if !filter_asm.is_empty() {
                mapping.retain(|(asm, _)| filter_asm.iter().any(|filter| asm.contains(filter)));
            }

            println!("Running...");

            let results = Progress::run(
                progress_data! {
                    P<'a> {
                        num_done: ProgressUsize = 0,
                        num_dasgupta_failed: ProgressUsize = 0,
                        not_equal: ProgressUsize = 0,
                        equal: ProgressUsize = 0,
                        liblisa_missing: ProgressUsize = 0,
                        dasgupta_missing: ProgressUsize = 0,
                        unsupported: ProgressUsize = 0,
                        total: usize = mapping.len(),
                        num_hits: &'a AtomicUsize = &*num_hits,
                        num_misses: &'a AtomicUsize = &*num_misses,
                    }, |f, P { num_done, num_dasgupta_failed, not_equal, equal, liblisa_missing, dasgupta_missing, unsupported, total, num_hits, num_misses }| write!(f, "Processed {num_done} / {total}: neq={not_equal} eq={equal} unsupported={unsupported}, missing: libLISA={liblisa_missing} dasgupta={dasgupta_missing}, no conversion={num_dasgupta_failed}; Cache: {num_hits:?} hits, {num_misses:?} misses")
                },
                |p| {
                    #[cfg(debug_assertions)]
                    let iter = mapping.iter();
                    #[cfg(not(debug_assertions))]
                    let iter = mapping.par_iter();
                    iter.map(|&(original_asm, instrs)| {
                        p.num_done.increment();
                        let asm: String = fix_instr(original_asm);
                        let asm = asm.trim();
                        debug!("Checking {asm}: {instrs:?}");

                        let mnemonic = asm.split(' ').next().unwrap();
                        trace!("Mnemonic: {mnemonic}");

                        let mut semantics = ComparisonResult {
                            instrs: instrs.clone(),
                            asm: asm.to_string(),
                            mnemonic: mnemonic.to_string(),
                            operand_types: Vec::new(),
                            dasgupta_path: None,
                            comparison_result: SemanticEquivalence::Timeout,
                        };

                        if is_unsupported_by_dasgupta(asm) {
                            // Nothing
                            trace!("Skipping {asm} because it contains register we do not support");
                            semantics.comparison_result = SemanticEquivalence::Unsupported;
                        } else if let Some(dasgupta_semantics) = dasgupta_semantics.get(mnemonic) {
                            // TODO: Maybe we can try to guess immediate size by inspecting encodings?
                            let operands = parse_operand_types(asm, mnemonic);

                            let sd = dasgupta_semantics
                                .iter()
                                .filter(|s| {
                                    s.operand_types.len() == operands.len()
                                        && s.operand_types
                                            .iter()
                                            .zip(operands.iter())
                                            .all(|(dasgupta_ty, (_, disasm_ty))| dasgupta_ty.matches(disasm_ty))
                                })
                                .max_by_key(|s| {
                                    let score = s
                                        .operand_types
                                        .iter()
                                        .zip(operands.iter())
                                        .map(|(dasgupta_ty, (_, disasm_ty))| dasgupta_ty.match_score(disasm_ty))
                                        .sum::<usize>() + if s.semantics.is_some() { 1 } else { 0 };

                                    debug!("Match score for {:?} ({:?}) vs {operands:?} = {score} (has semantics: {})", s.operand_types, s.file, s.semantics.is_some());

                                    score
                                });

                            if let Some(sd) = sd {
                                semantics.dasgupta_path = Some(sd.file.clone());
                                semantics.operand_types = sd.operand_types.clone();

                                info!(
                                    "\nFound semantics for {asm} (operands={:?}, sd.operand_types={:?}, path={:?})",
                                    operands, sd.operand_types, sd.file
                                );
                                if let Some(sd_semantics) = &sd.semantics {
                                    let mut liblisa_semantics = instrs
                                        .iter()
                                        .flat_map(|&(_, instr)| {
                                            instr_to_encoding[&instr].iter().map(move |&index| (index, instr))
                                        })
                                        .map(|(index, instr)| (&liblisa_semantics[index], instr))
                                        .collect::<Vec<_>>();
                                    liblisa_semantics.sort_by_key(|(_, instr)| *instr);

                                    let mut all_result = SemanticEquivalence::Equal;

                                    for (encoding, instr) in liblisa_semantics {
                                        assert!(encoding.bitpattern_as_filter().matches(&instr), "instruction list mismatch: please regenerate the instruction list from the encodings ({instr:X?} doesn't match {:?})", encoding.bitpattern_as_filter());
                                        let part_values =
                                            encoding.extract_parts(&instr).into_iter().map(Some).collect::<Vec<_>>();
                                        let instance = encoding.instantiate_partially(&part_values).unwrap();

                                        let operands = {
                                            // Fix jump offset for Dasgupta
                                            let mut v = operands.clone();
                                            if JUMP_INSTRS.contains(&mnemonic) {
                                                if let (
                                                    Operand::Imm {
                                                        val: imm_val, ..
                                                    },
                                                    RegType::Hex {
                                                        val: hex_val, ..
                                                    },
                                                ) = &mut v[0]
                                                {
                                                    *imm_val = imm_val.wrapping_sub(instr.byte_len() as i128);
                                                    *hex_val = hex_val.wrapping_sub(instr.byte_len() as u64);
                                                }
                                            }

                                            v
                                        };

                                        debug!("Comparing {instr:X} {asm}");
                                        trace!("part_values[{part_values:X?}] in {encoding}\n\n{sd:?}");
                                        let result = Z3Solver::with_thread_local(Duration::from_secs(900), |solver| {
                                            let mut solver = CachedSolver::new(solver, &solver_cache);
                                            compare_semantics(&mut solver, instance, sd_semantics, asm, &operands)
                                        });

                                        debug!("Comparison result for {instr:X} {asm}: {result:?}");

                                        if result != SemanticEquivalence::Equal {
                                            all_result = result;
                                            break
                                        }
                                    }

                                    match all_result {
                                        SemanticEquivalence::NotEqual | SemanticEquivalence::Timeout => p.not_equal.increment(),
                                        SemanticEquivalence::Equal => p.equal.increment(),
                                        SemanticEquivalence::LibLisaMissing => p.liblisa_missing.increment(),
                                        SemanticEquivalence::Unsupported => p.unsupported.increment(),
                                        _ => unreachable!(),
                                    }

                                    semantics.comparison_result = all_result;
                                } else {
                                    p.num_dasgupta_failed.increment();
                                    semantics.comparison_result = SemanticEquivalence::Unsupported;
                                }
                            } else {
                                info!("Unable to find Dasgupta's semantics for {asm:?}");
                                // Silence some known missing semantics
                                // let silent =
                                //     // Dasgupta does not have semantics for the ymm versions of these instructions
                                //     asm.contains("ymm") && ["vmpsadbw", "vpsignb", "vpsignw", "vpsignd", "vpminsw"].contains(&mnemonic)
                                //     // Dasgupta does not have semantics for mixed xmm/ymm versions of vcvtdq2pd
                                //     || asm.contains("ymm") && asm.contains("xmm") && mnemonic == "vcvtdq2pd"
                                //     // Dasgupta does not have semantics for retq_imm16
                                //     || mnemonic == "retq" && asm.contains("$0x");

                                // if !silent {
                                println!(
                                    "\nNo semantics for {asm}: looked for [{:?}], but couldn't find it in {:?}",
                                    operands.iter().map(|(_, x)| x).format(", "),
                                    dasgupta_semantics
                                        .iter()
                                        .map(|s| (&s.mnemonic, &s.operand_types))
                                        .format(", ")
                                );
                                // }
                                p.dasgupta_missing.increment();
                                semantics.comparison_result = SemanticEquivalence::DasguptaMissing;
                            }
                            //         if let Some(v) = v {
                            //             semantics.semantics = Some(v);
                            //             p.num_converted.increment();
                            //             p.num_ok.increment();
                            //         } else if ["%mm0", "%mm1", "%mm2", "%mm3", "%mm4", "%mm5", "%mm6", "%mm7", "%cs", "%ss", "%ds", "%es", "%fs", "%gs"].iter().any(|reg| asm.contains(reg))
                            //             || (asm.contains("ymm") && ["vmpsadbw ", "vpsignb ", "vpsignw ", "vpsignd ", "vpminsw "].iter().any(|s| asm.starts_with(s))) {
                            //             semantics.missing_in_dasgupta = true;
                            //         } else {
                            //             p.num_converted.increment();
                            //             println!("\nRewriting failed: {asm} => {op:?} {operands:?}");
                            //         }
                        } else {
                            debug!("No dasgupta semantics for {mnemonic} ({asm:?})");
                            p.dasgupta_missing.increment();
                            semantics.comparison_result = SemanticEquivalence::DasguptaMissing;
                        }

                        trace!("Final comparison result: {:?}", semantics.comparison_result);

                        semantics
                    })
                    .collect::<Vec<_>>()
                },
            );

            // let mut missed_dasgupta = flat_dasgupta_semantics.iter()
            //     .map(|f| (f.mnemonic.clone(), f.operand_types.clone()))
            //     .collect::<HashSet<_>>();

            // for item in results.iter() {
            //     let tmp1;
            //     let tmp2;
            //     let synonyms = match item.mnemonic.as_str() {
            //         "cmovnzq" => [ "cmovne" ].as_slice(),
            //         "setnbe" => &[ "seta" ],
            //         "jnbe" => &[ "ja" ],
            //         ccop if !ccop.starts_with("jmp") && ["set", "j", "cmov"].iter().any(|o| ccop.starts_with(o)) => {
            //             let tail = ccop.strip_prefix("set")
            //                 .or(ccop.strip_prefix('j'))
            //                 .or(ccop.strip_prefix("cmov"))
            //                 .unwrap();
            //             let head = ccop.strip_suffix(tail).unwrap();
            //             let (tail, suffix) = if let Some(t) = tail.strip_suffix('q') {
            //                 (t, "q")
            //             } else if let Some(t) = tail.strip_suffix('w') {
            //                 (t, "w")
            //             } else if let Some(t) = tail.strip_suffix('d') {
            //                 (t, "d")
            //             } else if let Some(t) = tail.strip_suffix('l') {
            //                 if !t.is_empty() {
            //                     (t, "l")
            //                 } else {
            //                     (tail, "")
            //                 }
            //             } else if let Some(t) = tail.strip_suffix('b') {
            //                 if !t.is_empty() {
            //                     (t, "b")
            //                 } else {
            //                     (tail, "")
            //                 }
            //             } else {
            //                 (tail, "")
            //             };
            //             let alternate_tail = match tail {
            //                 "p" | "pe" => "p",
            //                 "np" | "po" => "po",
            //                 "l" | "nge" => "l",
            //                 "ge" | "nl" => "ge",
            //                 "le" | "ng" => "ng",
            //                 "g" | "nle" => "nle",
            //                 "o" => "o",
            //                 "no" => "no",
            //                 "b" | "c" | "nae" => "nae",
            //                 "ae" | "nb" | "nc" => "nb",
            //                 "e" | "z" => "z",
            //                 "ne" | "nz" => "nz",
            //                 "be" | "na" => "na",
            //                 "a" | "nbe" => "nbe",
            //                 "s" => "s",
            //                 "ns" => "ns",
            //                 "cxz" | "ecxz" | "rcxz" => tail,
            //                 _ => todo!("tail {tail} for {ccop}"),
            //             };

            //             tmp1 = format!("{head}{alternate_tail}{suffix}");
            //             tmp2 = [ tmp1.as_str() ];

            //             &tmp2
            //         },
            //         "shll" | "sall" => &[ "shll", "sall" ],
            //         "shlq" | "salq" => &[ "shlq", "salq" ],
            //         "shlw" | "salw" => &[ "shlw", "salw" ],
            //         _ => &[],
            //     };

            //     for mnemonic in once(item.mnemonic.as_str()).chain(synonyms.iter().copied()) {
            //         missed_dasgupta.retain(|(m, t)| m != mnemonic
            //             || t.len() != item.operand_types.len()
            //             || !t.iter().zip(item.operand_types.iter()).all(|(a, b)| a.matches(b))
            //         );
            //     }
            // }

            // for (mnemonic, ot) in missed_dasgupta.iter() {
            //     println!("Missed: {mnemonic} {ot:?} -- available were: {:?}", results.iter()
            //         .filter(|r| r.mnemonic == *mnemonic)
            //         .map(|r| (&r.asm, &r.operand_types))
            //         .format(", ")
            //     );
            // }
            // println!("Missed dasgupta semantics: {}", missed_dasgupta.len());

            println!("Writing results...");
            if let Some(output) = output {
                serde_json::to_writer(BufWriter::new(File::create(output).unwrap()), &results).unwrap();
            } else {
                println!("Warning: not saving results, because --output was not specified");
            }
        },
        Args::CheckDisasm {
            instr,
        } => {
            let mut disassembler = Disassembler::new(libopcodes_rs::Arch::I386, false, libopcodes_rs::Mach::X86_64).unwrap();
            let asm = disassembler.disassemble(instr.bytes()).collect::<Vec<_>>();
            if asm.len() != 1 || asm[0].1.trim().starts_with("(bad)") {
                println!("unable to decode: {instr:X?} vs {asm:02X?}");
            } else {
                let asm = asm[0].1.clone();
                println!("original asm: {asm}");
                let asm = fix_instr(&asm);
                let asm = asm.trim();
                println!("fixed instr: {asm}");
                let mnemonic = asm.split(' ').next().unwrap();
                let ops = parse_operand_types(asm, mnemonic);
                println!("operands: {ops:#?}");
                println!("is_unsupported_by_dasgupta = {}", is_unsupported_by_dasgupta(asm));
            }
        },
        Args::GenerateTable {
            comparison,
            instrs,
            debug,
            semantics,
            k_semantics,
            dasgupta_semantics,
            latex,
        } => {
            eprintln!("Enumerating semantics files...");
            let files = find_dasgupta_semantics_files(k_semantics);

            eprintln!("Loading comparison results...");
            let comparison: Vec<ComparisonResult> =
                serde_json::from_reader(BufReader::new(File::open(comparison).unwrap())).unwrap();

            eprintln!("Loading libLISA semantics...");
            let liblisa_semantics: Vec<Encoding<X64Arch, SynthesizedComputation>> =
                serde_json::from_reader(BufReader::new(File::open(semantics).unwrap())).unwrap();
            let ExtractedInstrs {
                instrs, ..
            } = serde_json::from_reader(BufReader::new(File::open(instrs).unwrap())).unwrap();
            let instr_to_encoding = {
                let mut map = HashMap::new();
                for ((_, instr), indices) in instrs.iter() {
                    map.entry(*instr).or_insert_with(Vec::new).extend(indices.iter().copied());
                }

                map
            };

            eprintln!("Loading Dasgupta's semantics...");
            let mut deserializer = serde_json::Deserializer::from_reader(File::open(dasgupta_semantics).unwrap());
            deserializer.disable_recursion_limit();
            let flat_dasgupta_semantics = Vec::<DasguptaSemantic>::deserialize(&mut deserializer).unwrap();
            let parsed_dasgupta_semantic_files = flat_dasgupta_semantics
                .iter()
                .filter(|d| d.semantics.is_some())
                .map(|d| &d.file)
                .collect::<HashSet<_>>();

            let mut map = HashMap::new();

            for result in comparison.iter() {
                map.entry(&result.dasgupta_path).or_insert(Vec::new()).push(result);
            }

            eprintln!("Computing...");
            let mut v_agree = HashSet::new();
            let mut v_disagree = HashMap::new();
            let mut v_disagree_timeouts = HashSet::new();
            let mut v_missing_synthesis = HashSet::new();
            let mut v_skipped = HashSet::new();
            let mut e_disagree = HashSet::new();
            let mut e_missing = HashSet::new();

            for (k, v) in map.iter() {
                match k {
                    Some(path) => {
                        let unsupported = v.iter().any(|r| r.comparison_result == SemanticEquivalence::Unsupported);
                        let liblisa_missing = v.iter().any(|r| r.comparison_result == SemanticEquivalence::LibLisaMissing);
                        let is_agree = v.iter().all(|r| r.comparison_result == SemanticEquivalence::Equal);
                        if liblisa_missing {
                            v_missing_synthesis.insert(path);
                        } else if unsupported {
                            println!("Unsupported: {path:?}");
                            v_skipped.insert(path);
                        } else if is_agree {
                            v_agree.insert(path);
                        } else {
                            let num_disagreeing = v
                                .iter()
                                .filter(|r| r.comparison_result == SemanticEquivalence::NotEqual)
                                .count();
                            v_disagree.insert(path, (num_disagreeing, v.len()));
                            e_disagree.extend(
                                v.iter()
                                    .flat_map(|r| r.instrs.iter().flat_map(|(_, instr)| instr_to_encoding[instr].iter()))
                                    .copied(),
                            );

                            if v.iter().all(|r| {
                                r.comparison_result == SemanticEquivalence::Timeout
                                    || r.comparison_result == SemanticEquivalence::Equal
                            }) {
                                v_disagree_timeouts.insert(path);
                            }
                        }
                    },
                    None => {
                        for result in v {
                            for (_, instr) in result.instrs.iter() {
                                e_missing.extend(instr_to_encoding[instr].iter().copied());

                                if debug {
                                    for &index in instr_to_encoding[instr].iter() {
                                        eprintln!("Missing: {}", liblisa_semantics[index]);
                                    }
                                }
                            }
                        }
                    },
                }

                eprintln!("{k:?}: {:?}", v.iter().map(|v| v.comparison_result).collect::<HashSet<_>>());
            }

            for f in files.iter() {
                if !parsed_dasgupta_semantic_files.iter().any(|&d| d == f) {
                    println!("Not parsed: {f:?}");
                    v_skipped.insert(f);
                }
            }

            let mut v_missing_enumeration = parsed_dasgupta_semantic_files
                .iter()
                .filter(|&path| {
                    if v_agree.contains(path)
                        || v_disagree.contains_key(path)
                        || v_missing_synthesis.contains(path)
                        || v_skipped.contains(path)
                    {
                        false
                    } else {
                        let alias_sets = [
                            &["/sal", "/shl"] as &[&str],
                            &["/loopnz_", "/loopne_"],
                            &["/loopz_", "/loope_"],
                            &["/ja_", "/jnbe_"],
                            &["/jae_", "/jnb_", "/jnc_"],
                            &["/jnae_", "/jb_", "/jc_"],
                            &["/jbe_", "/jna_"],
                            &["/jcxz_", "/jecxz_", "/jrcxz_"],
                            &["/je_", "/jz_"],
                            &["/jg_", "/jnle_"],
                            &["/jge_", "/jnl_"],
                            &["/jl_", "/jnge_"],
                            &["/jle_", "/jng_"],
                            &["/jne_", "/jnz_"],
                            &["/jnp_", "/jpo_"],
                            &["/jp_", "/jpe_"],
                            &["/jmp_", "/jmpq_"],
                            &["/seta_", "/setnbe_"],
                            &["/setae_", "/setnb_", "/setnc_"],
                            &["/setnae_", "/setb_", "/setc_"],
                            &["/setbe_", "/setna_"],
                            &["/setcxz_", "/setecxz_", "/setrcxz_"],
                            &["/sete_", "/setz_"],
                            &["/setg_", "/setnle_"],
                            &["/setge_", "/setnl_"],
                            &["/setl_", "/setnge_"],
                            &["/setle_", "/setng_"],
                            &["/setne_", "/setnz_"],
                            &["/setnp_", "/setpo_"],
                            &["/setp_", "/setpe_"],
                            &["/cmoval_", "/cmovnbel_"],
                            &["/cmovael_", "/cmovnbl_", "/cmovncl_"],
                            &["/cmovnael_", "/cmovbl_", "/cmovcl_"],
                            &["/cmovbel_", "/cmovnal_"],
                            &["/cmovcxzl_", "/cmovecxzl_", "/cmovrcxzl_"],
                            &["/cmovel_", "/cmovzl_"],
                            &["/cmovgl_", "/cmovnlel_"],
                            &["/cmovgel_", "/cmovnll_"],
                            &["/cmovll_", "/cmovngel_"],
                            &["/cmovlel_", "/cmovngl_"],
                            &["/cmovnel_", "/cmovnzl_"],
                            &["/cmovnpl_", "/cmovpol_"],
                            &["/cmovpl_", "/cmovpel_"],
                            &["/cmovaq_", "/cmovnbeq_"],
                            &["/cmovaeq_", "/cmovnbq_", "/cmovncq_"],
                            &["/cmovnaeq_", "/cmovbq_", "/cmovcq_"],
                            &["/cmovbeq_", "/cmovnaq_"],
                            &["/cmovcxzq_", "/cmovecxzq_", "/cmovrcxzq_"],
                            &["/cmoveq_", "/cmovzq_"],
                            &["/cmovgq_", "/cmovnleq_"],
                            &["/cmovgeq_", "/cmovnlq_"],
                            &["/cmovlq_", "/cmovngeq_"],
                            &["/cmovleq_", "/cmovngq_"],
                            &["/cmovneq_", "/cmovnzq_"],
                            &["/cmovnpq_", "/cmovpoq_"],
                            &["/cmovpq_", "/cmovpeq_"],
                            &["/leaw_r16_m16", "/leaw_r16_m32", "/leaw_r16_m64"],
                            &["/leal_r32_m16", "/leal_r32_m32", "/leal_r32_m64"],
                            &["/leaq_r64_m16", "/leaq_r64_m32", "/leaq_r64_m64"],
                            &["/lodsb.k", "/lodsb_m8.k"],
                            &["/lodsw.k", "/lodsw_m16.k"],
                            &["/lodsl.k", "/lodsl_m32.k"],
                            &["/lodsq.k", "/lodsq_m64.k"],
                            &["/movsb.k", "/movsb_m8_m8.k"],
                            &["/movsw.k", "/movsw_m16_m16.k"],
                            &["/movsl.k", "/movsl_m32_m32.k"],
                            &["/movsq.k", "/movsq_m64_m64.k"],
                            &["/scasb.k", "/scasb_m8.k"],
                            &["/scasw.k", "/scasw_m16.k"],
                            &["/scasl.k", "/scasl_m32.k"],
                            &["/scasq.k", "/scasq_m64.k"],
                            &["/stosb.k", "/stosb_m8.k"],
                            &["/stosw.k", "/stosw_m16.k"],
                            &["/stosl.k", "/stosw_m32.k"], // note: typo in filename
                            &["/stosq.k", "/stosw_m64.k"], // note: typo in filename
                            &["/cmpsb.k", "/cmpsb_m8_m8.k"],
                            &["/cmpsw.k", "/cmpsw_m16_m16.k"],
                            &["/cmpsl.k", "/cmpsl_m32_m32.k"],
                            &["/cmpsq.k", "/cmpsq_m64_m64.k"],
                            &["/xchgb_r8_m8.k", "/xchgb_m8_r8.k"],
                            &["/xchgb_rh_m8.k", "/xchgb_m8_rh.k"],
                            &["/xchgw_r16_m16.k", "/xchgw_m16_r16.k"],
                            &["/xchgl_r32_m32.k", "/xchgl_m32_r32.k"],
                            &["/xchgq_r64_m64.k", "/xchgq_m64_r64.k"],
                            &["/xchgq_rax_r64.k", "/xchgq_r64_rax.k"],
                            &["/vpextrw_r64_xmm_imm8.k", "/vpextrw_r32_xmm_imm8.k"],
                            &["/vpextrb_r64_xmm_imm8.k", "/vpextrb_r32_xmm_imm8.k"],
                        ];

                        for aliases in alias_sets.iter() {
                            for from in aliases.iter() {
                                if path.as_os_str().to_str().unwrap().contains(from) {
                                    for to in aliases.iter() {
                                        if from != to {
                                            let other = PathBuf::from(path.as_os_str().to_str().unwrap().replace(from, to));
                                            if v_agree.contains(&other) {
                                                v_agree.insert(path);
                                                return false
                                            } else if let Some(v) = v_disagree.get(&other) {
                                                v_disagree.insert(path, *v);
                                                if v_disagree_timeouts.contains(&other) {
                                                    v_disagree_timeouts.insert(path);
                                                }

                                                return false
                                            } else if v_missing_synthesis.contains(&other) {
                                                v_missing_synthesis.insert(path);
                                                return false
                                            } else if v_skipped.contains(&other) {
                                                v_skipped.insert(path);
                                                return false
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        true
                    }
                })
                .collect::<HashSet<_>>();

            let mut v_missing_dasgupta_error = HashSet::new();

            let mut v_missing_out_of_scope = HashSet::new();
            v_missing_enumeration.retain(|&&path| {
                let sd = flat_dasgupta_semantics.iter().find(|s| &s.file == path).unwrap();

                if [
                    "systemInstructions/jecxz_rel32.k",
                    "systemInstructions/jrcxz_rel32.k",
                    "systemInstructions/vcvtdq2pd_ymm_ymm.k",
                    "vcvtpd2ps_xmm_m256.k",
                    "vcvtpd2ps_xmm_m128.k",
                    "vcvttpd2dq_xmm_m256.k",
                    "vcvttpd2dq_xmm_m128.k",
                    "vpinsrq_xmm_xmm_m64_imm8",
                    "vpinsrq_xmm_m64_imm8",
                    "vcvtdq2pd_ymm_ymm.k",
                ]
                .iter()
                .any(|s| path.to_str().unwrap().contains(s))
                {
                    v_missing_dasgupta_error.insert(path);
                    false
                } else if figure_out_if_semantic_is_in_scope(&sd.mnemonic, &sd.operand_types) {
                    true
                } else {
                    v_missing_out_of_scope.insert(path);
                    false
                }
            });

            v_disagree.retain(|&path, _| {
                let remove = [
                    "memoryInstructions/cld.k",
                    "memoryInstructions/std.k",
                    "memoryInstructions/popq_m64.k",
                ]
                .iter()
                .any(|s| path.to_str().unwrap().contains(s));

                if remove {
                    v_skipped.insert(path);
                }

                !remove
            });

            let v_extra_agree_with_scope_extension = v_missing_out_of_scope
                .iter()
                .filter(|&&path| {
                    let path_str = path.to_str().unwrap();
                    let in_scope_names = [
                        PathBuf::from(path_str.replace("w_", "q_").replace("r16", "r64").replace("m16", "m64")),
                        PathBuf::from(path_str.replace("w_", "l_").replace("r16", "r32").replace("m16", "m32")),
                        {
                            let dir = path.parent().unwrap();
                            let fname = path.file_name().unwrap().to_str().unwrap();
                            let mut fname_parts = fname.split('_').collect::<Vec<_>>();
                            if fname_parts.len() > 1 {
                                fname_parts.insert(1, fname_parts[1]);
                            }

                            dir.join(format!("v{}", fname_parts.join("_")))
                        },
                    ];

                    let found = in_scope_names.iter().find(|name| v_agree.contains(name));
                    eprintln!("Potential In-scope names for {path:?}: {in_scope_names:#?} => {found:?}");

                    found.is_some()
                })
                .collect::<HashSet<_>>();

            let v_disagree_only = v_disagree
                .iter()
                .filter(|(_, (n, _))| *n > 0)
                .map(|(&k, &v)| (k, v))
                .collect::<HashMap<_, _>>();

            eprintln!(
                "True disagreements ({}): {:#?}",
                v_disagree_only.len(),
                v_disagree_only.keys().sorted().collect::<Vec<_>>()
            );
            eprintln!("Timeouts: {v_disagree_timeouts:?}");
            eprintln!(
                "Disagreements that are not timeouts and not true disagreements: {:?}",
                v_disagree
                    .iter()
                    .filter(|(d, _)| !v_disagree_only.contains_key(*d) && !v_disagree_timeouts.contains(*d))
                    .sorted()
                    .collect::<HashMap<_, _>>()
            );
            let avg_disagree_percentage =
                v_disagree_only.values().map(|&(n, t)| n as f64 / t as f64).sum::<f64>() / v_disagree.len() as f64 * 100f64;

            eprintln!("Total number of Dasgupta semantics files: {}", files.len());
            eprintln!("Variants not enumerated: {v_missing_enumeration:#?}");

            let (v_disagree_dasgupta_error, v_disagree_liblisa_error): (HashSet<_>, HashSet<_>) =
                v_disagree_only.keys().copied().partition(|d| {
                    [
                        "immediateInstructions/rclb_r8_imm8.k",
                        "immediateInstructions/rclb_rh_imm8.k",
                        "immediateInstructions/rcrb_r8_imm8.k",
                        "immediateInstructions/rcrb_rh_imm8.k",
                        "memoryInstructions/rclb_m8_imm8.k",
                        "memoryInstructions/rcrb_m8_imm8.k",
                        "registerInstructions/rclb_r8_cl.k",
                        "registerInstructions/rclb_rh_cl.k",
                        "registerInstructions/rcrb_r8_cl.k",
                        "registerInstructions/rcrb_rh_cl.k",
                        "memoryInstructions/btcl_m32_r32.k",
                        "memoryInstructions/btcq_m64_r64.k",
                        "memoryInstructions/btl_m32_r32.k",
                        "memoryInstructions/btq_m64_r64.k",
                        "memoryInstructions/btrl_m32_r32.k",
                        "memoryInstructions/btrq_m64_r64.k",
                        "memoryInstructions/btsl_m32_r32.k",
                        "memoryInstructions/btsq_m64_r64.k",
                        "memoryInstructions/cmpsb.k",
                        "memoryInstructions/cmpsb_m8_m8.k",
                        "memoryInstructions/cmpsl.k",
                        "memoryInstructions/cmpsl_m32_m32.k",
                        "memoryInstructions/cmpsq.k",
                        "memoryInstructions/cmpsq_m64_m64.k",
                        "memoryInstructions/vmpsadbw_xmm_xmm_m128_imm8.k",
                        "registerInstructions/mulxl_r32_r32_r32.k",
                        "registerInstructions/mulxq_r64_r64_r64.k",
                        "registerInstructions/xchgl_r32_eax.k",
                        "registerInstructions/xchgl_eax_r32.k",
                        "systemInstructions/ja_rel32.k",
                        "systemInstructions/jnbe_rel32.k",
                    ]
                    .iter()
                    .any(|x| d.to_str().unwrap().contains(x))
                });

            eprintln!(
                "libLISA-caused disagreements ({}): {:#?}",
                v_disagree_liblisa_error.len(),
                v_disagree_liblisa_error.iter().sorted().collect::<Vec<_>>()
            );
            eprintln!(
                "Dasgupta-caused disagreements ({}): {:#?}",
                v_disagree_dasgupta_error.len(),
                v_disagree_dasgupta_error.iter().sorted().collect::<Vec<_>>()
            );
            eprintln!(
                "Invalid dasgupta specifications ({}): {:#?}",
                v_missing_dasgupta_error.len(),
                v_missing_dasgupta_error.iter().sorted().collect::<Vec<_>>()
            );

            if latex {
                println!("\\newcommand\\dasguptaVAgree{{{}}}", v_agree.len());
                println!(
                    "\\newcommand\\dasguptaVExtraAgreeWithScopeExtension{{{}}}",
                    v_extra_agree_with_scope_extension.len()
                );
                println!("\\newcommand\\dasguptaVDisagree{{{}}}", v_disagree.len());
                println!(
                    "\\newcommand\\dasguptaVDisagreeLibLisaError{{{}}}",
                    v_disagree_liblisa_error.len()
                );
                println!(
                    "\\newcommand\\dasguptaVDisagreeDasguptaError{{{}}}",
                    v_disagree_dasgupta_error.len()
                );
                println!("\\newcommand\\dasguptaVDisagreeTimeout{{{}}}", v_disagree_timeouts.len());
                println!("\\newcommand\\dasguptaEDisagree{{{}}}", e_disagree.len());
                println!("\\newcommand\\dasguptaDisagreeEncodingPercentage{{{avg_disagree_percentage:.2}}}");
                println!(
                    "\\newcommand\\dasguptaVMissingDasguptaError{{{}}}",
                    v_missing_dasgupta_error.len()
                );
                println!("\\newcommand\\dasguptaVMissingEnumeration{{{}}}", v_missing_enumeration.len());
                println!("\\newcommand\\dasguptaVMissingOutOfScope{{{}}}", v_missing_out_of_scope.len());
                println!("\\newcommand\\dasguptaVMissingSynthesis{{{}}}", v_missing_synthesis.len());
                println!("\\newcommand\\dasguptaVSkipped{{{}}}", v_skipped.len());
                println!("\\newcommand\\dasguptaEMissing{{{}}}", e_missing.len());
            } else {
                println!("v_agree: {}", v_agree.len());
                println!(
                    "v_extra_agree_with_scope_extension: {}",
                    v_extra_agree_with_scope_extension.len()
                );
                println!("v_disagree: {}", v_disagree.len());
                println!("v_disagree_liblisa_error: {}", v_disagree_liblisa_error.len());
                println!("v_disagree_dasgupta_error: {}", v_disagree_dasgupta_error.len());
                println!("v_disagree_timeout: {}", v_disagree_timeouts.len());
                println!("e_disagree: {}", e_disagree.len());
                println!("v_disagree: avg {avg_disagree_percentage:.2}% of encodings disagree per variant");
                println!("v_missing_dasgupta_error: {}", v_missing_dasgupta_error.len());
                println!("v_missing_out_of_scope: {}", v_missing_out_of_scope.len());
                println!("v_missing_enumeration: {}", v_missing_enumeration.len());
                println!("v_missing_synthesis: {}", v_missing_synthesis.len());
                println!("v_skipped: {}", v_skipped.len());
                println!("e_missing: {}", e_missing.len());
            }

            // for result in comparison.iter() {
            //     println!("{:?}: {:?}", result.dasgupta_path, result.comparison_result);
            // }
        },
    }
}

const JUMP_INSTRS: &[&str] = &[
    "loop", "loope", "loopne", "ja", "jae", "jb", "jbe", "jc", "jcxz", "jecxz", "jrcxz", "je", "jg", "jge", "jl", "jle", "jna",
    "jnae", "jnb", "jnbe", "jnc", "jne", "jng", "jnl", "jnle", "jno", "jnp", "jns", "jnz", "jo", "jp", "jpe", "jpo", "js", "jz",
    "jmp", "call",
];

fn is_unsupported_by_dasgupta(asm: &str) -> bool {
    !["lods", "movs", "scas", "stos", "cmps"]
        .iter()
        .any(|prefix| asm.starts_with(prefix))
        && [
            // Dasgupta doesn't support mmx registers (not to be confused with xmm registers)
            "%mm",
            // Dasgupta doesn't support segment registers (though I guess they *may* support them in memory addresses)
            // TODO: Figure out if we need to handle segments in memory addresses
            "%cs",
            "%ds",
            "%ss",
            "%fs",
            "%gs",
            "%es:",
            "%es,",
            "%st",
            "%bnd",
            "(8087 only)",
            "(287 only)",
            "(387 only)",
            "(bad)",
        ]
        .iter()
        .any(|s| asm.contains(s))
}

pub fn parse_operand_types(asm: &str, mnemonic: &str) -> Vec<(Operand, RegType)> {
    let Some(operands) = asm.strip_prefix(mnemonic) else {
        panic!("Assembly {asm} does not start with mnemonic {mnemonic}");
    };
    let operands = operands.replace("%ds:", "").replace("%es:", "");
    let operands = split_operands(operands.trim());
    trace!("Operands: {operands:?}");
    let mut operands = operands
        .iter()
        .map(|&op| {
            if op.starts_with("0x")
                || op.starts_with("*0x")
                || op.starts_with("-0x")
                || op.starts_with("*-0x")
                || op.contains('(')
            {
                let mut started_with_star = false;
                let (offset, offset_str, s) = if let Some(offset) = op
                    .strip_prefix("0x")
                    .or(op.strip_prefix("*0x").inspect(|_| started_with_star = true))
                {
                    let mut s = offset.split('(');
                    let offset_str = s.next().unwrap();
                    (
                        i128::from_str_radix(offset_str, 16).unwrap(),
                        Some(offset_str),
                        s.next().unwrap_or(""),
                    )
                } else if let Some(offset) = op
                    .strip_prefix("-0x")
                    .or(op.strip_prefix("*-0x").inspect(|_| started_with_star = true))
                {
                    let mut s = offset.split('(');
                    let offset_str = s.next().unwrap();
                    (-i128::from_str_radix(offset_str, 16).unwrap(), None, s.next().unwrap_or(""))
                } else {
                    let op = op.strip_prefix('*').unwrap_or(op);
                    (0, None, op.strip_prefix('(').unwrap_or(op))
                };

                let mut calculation = HashMap::new();

                if !s.is_empty() {
                    trace!("Inner: {s}");
                    let mut regs = s.strip_suffix(')').unwrap().split(',');
                    let base = regs.next().unwrap();
                    trace!("Base: {base}");
                    if !base.is_empty() {
                        assert!(
                            base.starts_with('%'),
                            "unable to parse: {asm:?} => {operands:?} => offset={offset}, s={s}"
                        );
                        let reg = alias_to_full_reg(base);
                        let (reg, _) = translate_variable_name_to_reg(reg, &[]).unwrap();
                        if !reg.is_zero() {
                            let key = (reg, AddrTermSize::U64, 0);
                            *calculation.entry(key).or_insert(0) += 1;
                        }
                    }

                    let index = regs.next();
                    let scale = regs.next().unwrap_or("1").parse::<i128>().unwrap();
                    trace!("Index: {index:?}, scale: {scale:?}");
                    if let Some(index) = index {
                        assert!(
                            index.starts_with('%'),
                            "unable to parse: {asm:?} => {operands:?} => offset={offset}, s={s}"
                        );
                        let reg = alias_to_full_reg(index);
                        let (reg, _) = translate_variable_name_to_reg(reg, &[]).unwrap();
                        if !reg.is_zero() {
                            let key = (reg, AddrTermSize::U64, 0);
                            *calculation.entry(key).or_insert(0) += usize::try_from(scale).unwrap();
                        }
                    }
                } else {
                    assert!(!op.contains('('));

                    if !started_with_star && JUMP_INSTRS.contains(&mnemonic) {
                        // Dasgupta's work expects jumps to have immediates even though libopcodes disassembles it as memory offsets
                        return (
                            Operand::Imm {
                                val: offset,
                                size: 64,
                            },
                            RegType::Hex {
                                val: offset as u64,
                                num_bytes: Some({
                                    let num_guessed_bits = RegType::guess_val_size(offset as u64);
                                    let byte_len = (num_guessed_bits as usize + 7) / 8;

                                    if offset_str.unwrap_or("").starts_with('0')
                                        && num_guessed_bits > 0
                                        && (offset >> (byte_len * 8 - 1)) & 1 != 0
                                    {
                                        byte_len + 1
                                    } else {
                                        byte_len
                                    }
                                }),
                            },
                        )
                    }
                }

                (
                    Operand::Addr(MemAddr {
                        sum_of: calculation,
                        offset: if RegType::guess_val_size_i128(offset) <= 64 {
                            offset as i64
                        } else {
                            panic!("{asm} has offset that does not fit in i64: 0x{offset:X}");
                        },
                    }),
                    RegType::MemOffset,
                )
            } else if let Some(num_str) = op.strip_prefix("$0x") {
                let num = u64::from_str_radix(num_str, 16).unwrap();
                (
                    Operand::Imm {
                        val: num as i128,
                        size: 64,
                    },
                    RegType::Hex {
                        val: num,
                        num_bytes: Some({
                            let num_guessed_bits = RegType::guess_val_size(num);
                            let byte_len = (num_guessed_bits as usize + 7) / 8;

                            if num_str.starts_with('0') && num_guessed_bits > 0 && (num >> (byte_len * 8 - 1)) & 1 != 0 {
                                byte_len + 1
                            } else {
                                byte_len
                            }
                        }),
                    },
                )
            } else if let Some(num_str) = op.strip_prefix("$") {
                println!("Non-hex operand: {asm}");
                let num = num_str.parse::<u64>().unwrap();
                (
                    Operand::Imm {
                        val: num as i128,
                        size: 64,
                    },
                    RegType::Hex {
                        val: num,
                        num_bytes: None,
                    },
                )
            } else {
                let op = op.strip_prefix('*').unwrap_or(op);
                (Operand::Var(op.to_string()), RegType::from_str(op))
            }
        })
        .collect::<Vec<_>>();

    if [
        "rclb", "rcrb", "rolb", "rorb", "shlb", "shrb", "rclw", "rcrw", "rolw", "rorw", "shlw", "shrw", "rcll", "rcrl", "roll",
        "rorl", "shll", "shrl", "rclq", "rcrq", "rolq", "rorq", "shlq", "shrq",
    ]
    .contains(&mnemonic)
        && operands.len() == 1
    {
        operands.insert(
            0,
            (
                Operand::Imm {
                    val: 1,
                    size: 8,
                },
                RegType::Hex {
                    val: 1,
                    num_bytes: None,
                },
            ),
        );
    }

    if ["lodsb", "lodsw", "lodsl", "lodsq", "scasb", "scasw", "scasl", "scasq"].contains(&mnemonic) && operands.len() > 1 {
        operands.drain(1..);
    }

    if ["stosb", "stosw", "stosl", "stosq"].contains(&mnemonic) && operands.len() > 1 {
        operands.remove(0);
    }

    operands
}

fn figure_out_if_semantic_is_in_scope(mnemonic: &str, operand_types: &[RegType]) -> bool {
    if ["vmaskmovpd", "vmaskmovps", "vpmaskmovq", "vpmaskmovd"].contains(&mnemonic) {
        return false
    }

    let asm = format!(
        "{mnemonic} {}",
        operand_types
            .iter()
            .map(|ty| String::from(match ty {
                RegType::Al => "%al",
                RegType::Rh => "%bh",
                RegType::R8 => "%bl",
                RegType::R16 => "%bx",
                RegType::R32 => "%edi",
                RegType::R64 => "%rdi",
                RegType::Xmm => "%xmm1",
                RegType::Ymm => "%ymm1",
                RegType::Imm | RegType::Imm8 => "$0x11",
                RegType::Imm16 => "$0x1122",
                RegType::Imm32 => "$0x11223344",
                RegType::Imm64 => "$0x1122334455667788",
                RegType::Cl => "%cl",
                RegType::Ax => "%ax",
                RegType::Eax => "%eax",
                RegType::Rax => "%rax",
                RegType::Xmm0 => "%xmm0",
                RegType::X86Id => ".label",
                RegType::MemOffset => "(%rax)",
                RegType::Mm => "%mm",
                RegType::Mm0 => "%mm0",
                RegType::Hex {
                    val, ..
                } => return format!("$0x{val:X}"),
            }))
            .format(", ")
    );

    let mut compiled = std::process::Command::new("/usr/bin/gcc")
        .args(["-x", "assembler", "/dev/stdin", "-c", "-o", "tmp.out"])
        .stdin(Stdio::piped())
        .spawn()
        .unwrap();
    let mut input = compiled.stdin.take().unwrap();
    input.write_all(asm.as_bytes()).unwrap();
    input.write_all(b"\n").unwrap();
    drop(input);

    compiled.wait().unwrap();

    let output = std::process::Command::new("objcopy")
        .args(["-O", "binary", "-j", ".text", "tmp.out", "/dev/stdout"])
        .output()
        .unwrap();
    let bytes = output.stdout;

    eprintln!("{mnemonic} {operand_types:?} => {asm} => {bytes:02X?}");

    std::fs::remove_file("tmp.out").ok();

    PrefixScope.is_instr_in_scope(&bytes)
}

fn find_dasgupta_semantics_files(k_semantics: PathBuf) -> Vec<PathBuf> {
    let files = [
        "immediateInstructions",
        "memoryInstructions",
        "registerInstructions",
        "systemInstructions",
    ]
    .map(|dir| k_semantics.join(dir))
    .iter()
    .flat_map(|dir| {
        eprintln!("Reading {dir:?}");
        std::fs::read_dir(dir).expect("Directory not found")
    })
    .map(|item| item.unwrap().path())
    .filter(|item| !item.to_str().unwrap().contains("_label"))
    .collect::<Vec<_>>();
    files
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SemanticEquivalence {
    NotEqual,
    Equal,
    LibLisaMissing,
    Unsupported,
    Timeout,
    DasguptaMissing,
}
