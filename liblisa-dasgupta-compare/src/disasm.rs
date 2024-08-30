use std::collections::{HashMap, HashSet};

use arrayvec::ArrayVec;
use liblisa::Instruction;
use liblisa_progress::{progress_data, Progress, ProgressUsize};
use libopcodes_rs::Disassembler;
use log::debug;

#[derive(Clone, Debug, Default)]
pub struct Info {
    disasm_failed: bool,
    disasm_ok: bool,
}

pub fn libopcodes_disassemble(
    num_encodings: usize, instrs: Vec<((bool, Instruction), Vec<usize>)>,
) -> HashMap<String, HashSet<(bool, Instruction)>> {
    let mut disassembler = Disassembler::new(libopcodes_rs::Arch::I386, false, libopcodes_rs::Mach::X86_64).unwrap();

    let mut info = vec![Info::default(); num_encodings];

    let mapping = Progress::run(
        progress_data! {
            P {
                num_processed: ProgressUsize = 0,
                total: usize = instrs.len(),
            }, |f, P { num_processed, total }| write!(f, "Disassembling with libopcodes: {num_processed} / {total}")
        },
        |p| {
            let mut m = HashMap::<_, HashSet<_>>::new();
            for ((has_semantics, instr), encoding_indices) in instrs {
                let _d = p.num_processed.delayed_increment();

                let asm = disassembler.disassemble(instr.bytes()).collect::<ArrayVec<_, 8>>();
                if instr == Instruction::new(&[ 0x93 ]) {
                    println!("Disassembled: {asm:?}");
                }
                
                if asm.len() != 1 || asm[0].1.trim().starts_with("(bad)") {
                    debug!("libopcodes disagrees: {instr:X?} vs {asm:02X?}");

                    for index in encoding_indices {
                        info[index].disasm_failed = true;
                    }
                } else {
                    for index in encoding_indices {
                        info[index].disasm_ok = true;
                    }

                    m.entry(asm[0].1.clone()).or_default().insert((has_semantics, instr));
                }
            }

            m
        },
    );

    let num_complete_disasm_fails = info.iter().filter(|info| info.disasm_failed && !info.disasm_ok).count();
    let num_partial_disasm_fails = info.iter().filter(|info| info.disasm_failed && info.disasm_ok).count();

    println!("Processed {} encodings", num_encodings);
    println!(
        "Disassembly failed completely for {num_complete_disasm_fails} encodings, partially for {num_partial_disasm_fails} encodings"
    );
    println!("Disassembled into {} mnemonics", mapping.len());
    mapping
}
