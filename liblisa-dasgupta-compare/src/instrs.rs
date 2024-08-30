use std::collections::{HashMap, HashSet};

use arrayvec::ArrayVec;
use liblisa::arch::Arch;
use liblisa::encoding::Encoding;
use liblisa::semantics::Computation;
use liblisa::utils::EitherIter;
use liblisa::Instruction;
use liblisa_progress::{progress_data, Progress, ProgressUsize};
use libopcodes_rs::Disassembler;
use log::trace;
use rayon::prelude::*;
use regex::Regex;
use serde::{Deserialize, Serialize};

use crate::{is_unsupported_by_dasgupta, parse_operand_types};

pub fn extract_instrs<A: Arch, C: Computation + Send + Sync>(
    semantics: &[Encoding<A, C>],
) -> HashMap<(bool, Instruction), Vec<usize>> {
    let instrs = Progress::run(
        progress_data! {
            P {
                num_processed: ProgressUsize = 0,
                num_encodings: usize = semantics.len(),
            }, |f, P { num_processed, num_encodings }| write!(f, "Extracted random instructions: {num_processed:?} / {num_encodings}")
        },
        |p| {
            semantics
                .par_iter()
                .enumerate()
                .flat_map(|(index, e)| {
                    let mut disassembler =
                        Disassembler::new(libopcodes_rs::Arch::I386, false, libopcodes_rs::Mach::X86_64).unwrap();
                    let _d = p.num_processed.delayed_increment();

                    let best_instr = e.best_instr();
                    let mut rng = rand::thread_rng();
                    
                    let mut seen = HashMap::new();
                    let iter = if e.num_wildcard_bits() <= 13 {
                        EitherIter::Left(e.iter_instrs(&[ None; 64 ][..e.parts.len()], true))
                    } else {
                        EitherIter::Right(e.random_instrs(&[ None; 64 ][..e.parts.len()], &mut rng))
                    };

                    let mut instrs_seen = HashSet::new();

                    let random = iter.take(10_000)
                        .filter(|instr| instrs_seen.insert(*instr))
                        .filter(|instr| {
                            let key = {
                                let asm = disassembler.disassemble(instr.bytes()).collect::<ArrayVec<_, 8>>();
                                trace!("asm: {asm:?}");
                                if asm.len() != 1 || asm[0].1.trim().starts_with("(bad)") {
                                    None
                                } else {
                                    let asm = asm[0].1.trim();
                                    if is_unsupported_by_dasgupta(asm) {
                                        None
                                    } else {
                                        let asm = fix_instr(asm);
                                        let asm = asm.trim();
                                        let mnemonic = asm.split(' ').next().unwrap();
                                        let operands = parse_operand_types(asm, mnemonic);
                                        let mut equal_operands = operands
                                            .iter()
                                            .enumerate()
                                            .flat_map(|(a_index, (a_op, _))| {
                                                operands
                                                    .iter()
                                                    .enumerate()
                                                    .filter(move |(_, (b_op, _))| a_op == b_op)
                                                    .map(move |(b_index, _)| (a_index, b_index))
                                            })
                                            .collect::<Vec<_>>();
                                        equal_operands.sort();
                                        let operand_types = operands.into_iter().map(|(_, ty)| ty.anonymize()).collect::<Vec<_>>();

                                        Some((mnemonic.to_string(), operand_types, equal_operands))
                                    }
                                }
                            };

                            trace!("Key: {key:?}");

                            let num_seen = seen.entry(key).or_insert(0);
                            *num_seen += 1;
                            trace!("num_seen={num_seen}");

                            *num_seen <= 3
                        });
                    let has_semantics = e.all_outputs_have_computations();

                    let result = best_instr
                        .into_iter()
                        .chain(random)
                        .map(|instr| (index, (has_semantics, instr)))
                        .inspect(|(_, (_, instr))| assert!(instr.bit_len() == e.instr().bit_len()))
                        .collect::<Vec<_>>();

                    assert!(!result.is_empty());
                    result
                })
                .collect::<Vec<_>>()
        },
    );

    let mut map = HashMap::new();
    for (index, instr) in instrs {
        map.entry(instr).or_insert_with(Vec::new).push(index);
    }

    map
}

#[derive(Serialize, Deserialize)]
pub struct ExtractedInstrs {
    pub num_encodings: usize,
    pub instrs: Vec<((bool, Instruction), Vec<usize>)>,
}

fn strip_prefix_inplace(s: &mut String, prefix: &str) {
    if let Some(new) = s.strip_prefix(prefix) {
        *s = new.to_string();
    }
}

// adapted from: https://github.com/StanfordPL/stoke/blob/develop/src/disassembler/disassembler.cc
pub fn fix_instr(asm: &str) -> String {
    let mut s = asm.to_string();

    // Remove comments
    if let Some(pos) = s.find('#') {
        s = s[..pos].trim().to_string();
    }

    strip_prefix_inplace(&mut s, "lock ");
    strip_prefix_inplace(&mut s, "rex ");
    strip_prefix_inplace(&mut s, "{vex}w ");
    strip_prefix_inplace(&mut s, "{vex}l ");
    strip_prefix_inplace(&mut s, "{vex}r ");
    strip_prefix_inplace(&mut s, "{vex}x ");
    strip_prefix_inplace(&mut s, "{vex}b ");

    if let Some(rest) = s.strip_prefix("rex.") {
        let skip = rest.find(' ').unwrap();
        s = rest[skip..].trim().to_string();
    }

    const ROTS: &[&str] = &["shl", "shr", "sal", "sar", "rcl", "rcr", "rol", "ror"];
    if ROTS.iter().any(|&r| s.starts_with(r)) {
        let missing = s.find(',').is_none();
        let paren = s.find('(');

        let mut need_one = missing;
        if !missing && paren.is_some() {
            need_one = s[..paren.unwrap()].find(',').is_none();
        }

        if need_one {
            let split = s.find(' ').unwrap();
            s = format!("{} $0x1,{}", &s[..split], &s[split + 1..]);
        }
    }

    if s.starts_with("stos") {
        let comma = s.find(',').unwrap();
        return format!("{}{}", &s[..6], &s[comma + 1..])
    } else if s.starts_with("rep stos") {
        let comma = s.find(',').unwrap();
        return format!("{}{}", &s[..10], &s[comma + 1..])
    } else if s.starts_with("repnz scas") {
        let comma = s.find(',').unwrap();
        return s[..comma].to_string()
    }

    if s.starts_with("hlt") {
        return String::from("retq")
    } else if s.starts_with("repz retq") {
        return String::from("repz retq")
    } else if s.starts_with("data") || s.starts_with("nopq") {
        // nopq is missing from dasgupta, but it will be the same as all other nops.
        return String::from("nop")
    } else if let Some(rest) = s.strip_prefix("movabsq") {
        return format!("movq{rest}")
    } else if let Some(rest) = s.strip_prefix("movsx ") {
        return format!("movsbl {rest}")
    }

    if let Some(rest) = s.strip_prefix("callq ") {
        return format!("call {rest}")
    } else if let Some(rest) = s.strip_prefix("jmpq ") {
        return format!("jmp {rest}")
    }

    // if let Some(rest) = s.strip_prefix("vcmp_us") {
    //     return format!("vcmp{rest}")
    // }

    if s.starts_with("cmp") || s.starts_with("vcmp") {
        let mapping = [
            ("unord_s", "$$0x13"),
            ("unord", "$$0x03"),
            ("true_us", "$$0x1f"),
            ("true", "$$0x0f"),
            ("ord_s", "$$0x17"),
            ("ord", "$$0x07"),
            ("nlt_uq", "$$0x15"),
            ("nlt", "$$0x05"),
            ("nle_uq", "$$0x16"),
            ("nle", "$$0x06"),
            ("ngt_uq", "$$0x1a"),
            ("ngt", "$$0x0a"),
            ("nge_uq", "$$0x19"),
            ("nge", "$$0x09"),
            ("neq_us", "$$0x14"),
            ("neq_os", "$$0x1c"),
            ("neq_oq", "$$0x0c"),
            ("neq", "$$0x04"),
            ("lt_oq", "$$0x11"),
            ("lt", "$$0x01"),
            ("le_oq", "$$0x12"),
            ("le", "$$0x02"),
            ("gt_oq", "$$0x1e"),
            ("gt", "$$0x0e"),
            ("ge_oq", "$$0x1d"),
            ("ge", "$$0x0d"),
            ("false_os", "$$0x1b"),
            ("false", "$$0x0b"),
            ("eq_us", "$$0x18"),
            ("eq_uq", "$$0x08"),
            ("eq_os", "$$0x10"),
            ("eq", "$$0x0"),
        ];

        for (from, to) in mapping {
            let regex = Regex::new(&format!("(v?cmp){from}([^ ]+)")).unwrap();
            s = regex.replace(&s, format!("$1$2 {to},")).to_string();
        }
    }

    if s.starts_with("vcvt") {
        s = s.replace("vcvtpd2psx", "vcvtpd2ps");
        s = s.replace("vcvtpd2psy", "vcvtpd2ps");
        // We should only map this instruction for the non-memory variant
        if !s.contains("(") {
            s = s.replace("vcvtpd2dqx", "vcvtpd2dq");
        }
        s = s.replace("vcvtpd2dqy", "vcvtpd2dq");
        s = s.replace("vcvttpd2dqy", "vcvttpd2dq");
        s = s.replace("vcvttpd2dqx", "vcvttpd2dq");
        s = s.replace("vcvttss2siq", "vcvttss2si");
        s = s.replace("vcvttss2sil", "vcvttss2si");
        s = s.replace("vcvttsd2sil", "vcvttsd2si");
        s = s.replace("vcvttsd2siq", "vcvttsd2si");
        s = s.replace("vcvtsd2siq", "vcvtsd2si");
        s = s.replace("vcvtsd2sil", "vcvtsd2si");
        s = s.replace("vcvtss2siq", "vcvtsd2si");
        s = s.replace("vcvtss2sil", "vcvtsd2si");
    } else if s.starts_with("cvt") {
        s = s.replace("cvttss2siq", "cvttss2si");
        s = s.replace("cvttss2sil", "cvttss2si");
        s = s.replace("cvttsd2sil", "cvttsd2si");
        s = s.replace("cvttsd2siq", "cvttsd2si");
        s = s.replace("cvtsd2siq", "cvtsd2si");
        s = s.replace("cvtsd2sil", "cvtsd2si");
        s = s.replace("cvtss2siq", "cvtsd2si");
        s = s.replace("cvtss2sil", "cvtsd2si");
    } else if s.starts_with("mova") {
        let regex = Regex::new("movap([ds])\\.s").unwrap();
        s = regex.replace(&s, "movap$1").to_string();
    } else if s.starts_with("movu") {
        let regex = Regex::new("movup([ds])\\.s").unwrap();
        s = regex.replace(&s, "movup$1").to_string();
    } else if s.starts_with("vmova") {
        let regex = Regex::new("vmovap([ds])\\.s").unwrap();
        s = regex.replace(&s, "vmovap$1").to_string();
    } else if s.starts_with("vmovd") {
        let regex = Regex::new("vmovdq([ds])\\.s").unwrap();
        s = regex.replace(&s, "vmovdq$1").to_string();
    } else if s.starts_with("vmovu") {
        let regex = Regex::new("vmovup([ds])\\.s").unwrap();
        s = regex.replace(&s, "vmovup$1").to_string();
    } else if s.starts_with("movnti") {
        s = s.replace("movntil", "movnti");
        s = s.replace("movntiq", "movnti");
    }

    if let Some(rest) = s.strip_prefix("loopeq ") {
        return format!("loope {rest}")
    } else if let Some(rest) = s.strip_prefix("loopneq ") {
        return format!("loopne {rest}")
    } else if let Some(rest) = s.strip_prefix("loopq ") {
        return format!("loop {rest}")
    } else if let Some(rest) = s.strip_prefix("vpcmpestril ") {
        return format!("vpcmpestri {rest}")
    } else if let Some(rest) = s.strip_prefix("vpcmpestrml ") {
        return format!("vpcmpestrm {rest}")
    } else if let Some(rest) = s.strip_prefix("vpcmpestriq ") {
        return format!("vpcmpestri {rest}")
    } else if let Some(rest) = s.strip_prefix("vpcmpestrmq ") {
        return format!("vpcmpestrm {rest}")
    }

    s
}
