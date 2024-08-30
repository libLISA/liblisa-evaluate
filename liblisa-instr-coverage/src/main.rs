use std::collections::HashSet;
use std::ffi::CStr;
use std::fs::File;
use std::io::{BufReader, Write};
use std::path::PathBuf;

use clap::Parser;
use liblisa::arch::x64::{PrefixScope, X64Arch};
use liblisa::arch::Scope;
use liblisa::encoding::Encoding;
use liblisa::instr::FilterMap;
use liblisa::semantics::default::computation::SynthesizedComputation;
use liblisa::Instruction;

#[global_allocator]
static GLOBAL: jemallocator::Jemalloc = jemallocator::Jemalloc;

#[derive(clap::Parser)]
struct Args {
    encodings: PathBuf,

    #[clap(long = "instrs")]
    instructions: Vec<PathBuf>,

    #[clap(long = "table-out")]
    table_out: Option<PathBuf>,
}

#[derive(Copy, Clone, Default, Debug)]
struct Stats {
    not_synthesized: usize,

    // seen_correct: usize,
    seen_not_synthesized: usize,
    seen_ring0: usize,
    seen_out_of_scope: usize,
    seen_excluded: usize,

    missed: usize,
    ring0: usize,
    out_of_scope: usize,
    total: usize,
    total_in_scope: usize,
    excluded: usize,
    seen: usize,

    found_in_scope: usize,

    enum_covered: usize,

    found: usize,
}

impl Stats {
    pub fn completeness(&self) -> f64 {
        self.found as f64 * 100. / self.seen as f64
    }

    pub fn scoped_completeness(&self) -> f64 {
        self.found_in_scope as f64 * 100. / self.total_in_scope as f64
    }
}

pub fn normalize_instr(instr: Instruction) -> Instruction {
    let b = instr.bytes();
    match b {
        // CS & DS segment overrides are used as branch prediction hints; They don't affect the behavior of the code itself.
        [0x3E, ..] | [0x2E, ..] => normalize_instr(Instruction::from(&b[1..])),
        _ => Instruction::new(b),
    }
}

fn main() {
    env_logger::init();
    let args = Args::parse();
    let file = File::open(&args.encodings).unwrap();

    eprintln!("Loading encodings...");
    let encodings: Vec<Encoding<X64Arch, SynthesizedComputation>> = serde_json::from_reader(BufReader::new(file)).unwrap();

    eprintln!("Processing filters...");
    let mut filters = FilterMap::new();
    for (index, filter) in encodings
        .iter()
        .enumerate()
        .flat_map(|(index, e)| e.filters().into_iter().map(move |e| (index, e)))
    {
        filters.add(filter, index);
    }

    let mut num_instrs_checked = 0;
    let mut encodings_covered = HashSet::new();

    let (mmode, stack_addr_width) = (xed_sys::XED_MACHINE_MODE_LONG_64, xed_sys::XED_ADDRESS_WIDTH_64b);
    unsafe { xed_sys::xed_tables_init() }

    let mut iclasses_missed = HashSet::new();

    let mut all_stats = Vec::new();
    for instrs_file in args.instructions {
        eprint!("Loading {}", instrs_file.display());
        let mut scan_instrs: Vec<Instruction> =
            serde_json::from_reader(BufReader::new(File::open(&instrs_file).unwrap())).unwrap();
        scan_instrs.sort();
        scan_instrs.dedup();

        let stats = {
            let mut stats = Stats::default();
            for chunk in scan_instrs.chunks(10_000) {
                eprint!(".");
                std::io::stdout().lock().flush().unwrap();
                for instr in chunk.iter() {
                    num_instrs_checked += 1;
                    let instr = normalize_instr(*instr);
                    let mut iclass_name = None;
                    let mut instr_iclass = None;
                    let (is_ring0, out_of_scope_reg) = unsafe {
                        let itext = instr.bytes();
                        let mut xedd = ::std::mem::MaybeUninit::<xed_sys::xed_decoded_inst_t>::uninit();
                        xed_sys::xed_decoded_inst_zero(xedd.as_mut_ptr());
                        xed_sys::xed_decoded_inst_set_mode(xedd.as_mut_ptr(), mmode, stack_addr_width);

                        let xed_error: xed_sys::xed_error_enum_t =
                            xed_sys::xed_decode(xedd.as_mut_ptr(), itext.as_ptr(), itext.len() as u32);
                        let desc = std::ffi::CStr::from_ptr(xed_sys::xed_error_enum_t2str(xed_error)).to_string_lossy();
                        if xed_error == xed_sys::XED_ERROR_NONE {
                            let instr = xedd.assume_init();
                            let xi = xed_sys::xed_decoded_inst_inst(&instr);
                            let mut out_of_scope = false;
                            let iclass = xed_sys::xed_decoded_inst_get_iclass(&instr);
                            iclass_name = Some(CStr::from_ptr(xed_sys::xed_iclass_enum_t2str(iclass)));
                            instr_iclass = Some(iclass);
                            let var_name = is_out_of_scope(iclass);
                            out_of_scope |= var_name;

                            for n in 0..xed_sys::xed_decoded_inst_noperands(&instr) {
                                let op = xed_sys::xed_inst_operand(xi, n);
                                let op_name = xed_sys::xed_operand_name(op);
                                if xed_sys::xed_operand_is_register(op_name) != 0 {
                                    let reg_out_of_scope = is_reg_out_of_scope(instr, op_name);
                                    out_of_scope |= reg_out_of_scope;
                                }
                            }

                            let is_ring0 =
                                xed_sys::xed_decoded_inst_get_attribute(xedd.as_mut_ptr(), xed_sys::XED_ATTRIBUTE_RING0) == 1;
                            (is_ring0, out_of_scope)
                        } else {
                            eprintln!("error={} for {:02X?}", desc, instr.bytes());
                            (false, false)
                        }
                    };

                    let out_of_prefix_scope = !PrefixScope.is_instr_in_scope(instr.bytes());
                    let found = filters.filters(&instr);
                    if let Some(&index) = found {
                        encodings_covered.insert(index);
                    }

                    stats.seen += 1;
                    if found.is_some() {
                        stats.found += 1;
                    } else {
                        stats.missed += 1;
                        // eprintln!("Missed: {:02X?}", instr.bytes());
                    }

                    if is_ring0 {
                        stats.seen_ring0 += 1;
                    } else if out_of_scope_reg {
                        stats.seen_out_of_scope += 1;
                    } else if out_of_prefix_scope {
                        stats.seen_excluded += 1;
                    } else {
                        stats.seen_not_synthesized += 1;
                    }

                    if found.is_some() {
                        stats.enum_covered += 1;
                    }

                    if is_ring0 {
                        stats.ring0 += 1;
                    } else if out_of_scope_reg {
                        stats.out_of_scope += 1;
                    } else if out_of_prefix_scope {
                        stats.excluded += 1;
                    } else {
                        if found.is_some() {
                            stats.found_in_scope += 1;
                        } else {
                            eprintln!("MISSED In-scope: {:02X?} / {:?}", instr.bytes(), iclass_name);
                            if let Some(n) = instr_iclass {
                                iclasses_missed.insert(n);
                            }
                        }

                        stats.total_in_scope += 1;
                        stats.not_synthesized += 1;
                    }

                    stats.total += 1;
                }
            }

            eprintln!();

            stats
        };

        all_stats.push((instrs_file.file_stem().unwrap().to_string_lossy().to_string(), stats));

        eprintln!("done.");

        eprintln!(
            "Scoped completeness: {:3.2}%; Completeness: {:3.2}%; {:#?}",
            stats.scoped_completeness(),
            stats.completeness(),
            stats
        );
    }

    for iclass in iclasses_missed {
        let name = unsafe { CStr::from_ptr(xed_sys::xed_iclass_enum_t2str(iclass)) };
        println!("iclass missed (in-scope): {name:?}");
    }

    if let Some(path) = args.table_out {
        let mut f = File::create(path).unwrap();
        writeln!(f, "\\begin{{tabular}}{{|c|c c c c|c|}}").unwrap();
        writeln!(f, "\\hline").unwrap();
        writeln!(f, "Source & Total & Seen & Found & Missed & Completeness \\\\ [0.5ex] ").unwrap();
        writeln!(f, "\\hline\\hline").unwrap();

        for (name, stats) in all_stats.iter() {
            writeln!(
                f,
                "    {} & {} & {} & {} & {} & {:3.2}\\%\\\\",
                name,
                stats.total,
                stats.seen,
                stats.found,
                stats.missed,
                stats.completeness(),
            )
            .unwrap();
        }

        writeln!(f, "\\hline").unwrap();
        writeln!(f, "\\end{{tabular}}").unwrap();
    }

    let all_coverage =
        (all_stats.iter().map(|(_, stat)| stat.completeness()).sum::<f64>() / all_stats.len() as f64 * 100.0).floor() / 100.0;
    let scoped_coverage =
        (all_stats.iter().map(|(_, stat)| stat.scoped_completeness()).sum::<f64>() / all_stats.len() as f64 * 100.0).floor()
            / 100.0;
    println!("Total instructions: {num_instrs_checked}");
    println!("Total encodings covered: {}", encodings_covered.len());
    println!("Average coverage (all): {all_coverage:3.2}");
    println!("Average coverage (in-scope): {scoped_coverage:3.2}");
}

fn is_reg_out_of_scope(instr: xed_sys::xed_decoded_inst_s, op_name: u32) -> bool {
    match unsafe { xed_sys::xed_decoded_inst_get_reg(&instr, op_name) } {
        xed_sys::XED_REG_INVALID
        | xed_sys::XED_REG_BNDCFGU
        | xed_sys::XED_REG_BNDSTATUS
        | xed_sys::XED_REG_BND0
        | xed_sys::XED_REG_BND1
        | xed_sys::XED_REG_BND2
        | xed_sys::XED_REG_BND3
        | xed_sys::XED_REG_CR0
        | xed_sys::XED_REG_CR1
        | xed_sys::XED_REG_CR2
        | xed_sys::XED_REG_CR3
        | xed_sys::XED_REG_CR4
        | xed_sys::XED_REG_CR5
        | xed_sys::XED_REG_CR6
        | xed_sys::XED_REG_CR7
        | xed_sys::XED_REG_CR8
        | xed_sys::XED_REG_CR9
        | xed_sys::XED_REG_CR10
        | xed_sys::XED_REG_CR11
        | xed_sys::XED_REG_CR12
        | xed_sys::XED_REG_CR13
        | xed_sys::XED_REG_CR14
        | xed_sys::XED_REG_CR15
        | xed_sys::XED_REG_DR0
        | xed_sys::XED_REG_DR1
        | xed_sys::XED_REG_DR2
        | xed_sys::XED_REG_DR3
        | xed_sys::XED_REG_DR4
        | xed_sys::XED_REG_DR5
        | xed_sys::XED_REG_DR6
        | xed_sys::XED_REG_DR7
        | xed_sys::XED_REG_ERROR
        | xed_sys::XED_REG_K0
        | xed_sys::XED_REG_K1
        | xed_sys::XED_REG_K2
        | xed_sys::XED_REG_K3
        | xed_sys::XED_REG_K4
        | xed_sys::XED_REG_K5
        | xed_sys::XED_REG_K6
        | xed_sys::XED_REG_K7
        | xed_sys::XED_REG_SSP
        | xed_sys::XED_REG_IA32_U_CET
        | xed_sys::XED_REG_MXCSR
        | xed_sys::XED_REG_GDTR
        | xed_sys::XED_REG_LDTR
        | xed_sys::XED_REG_IDTR
        | xed_sys::XED_REG_TR
        | xed_sys::XED_REG_TSC
        | xed_sys::XED_REG_TSCAUX
        | xed_sys::XED_REG_MSRS
        | xed_sys::XED_REG_ES
        | xed_sys::XED_REG_CS
        | xed_sys::XED_REG_SS
        | xed_sys::XED_REG_DS
        | xed_sys::XED_REG_FS
        | xed_sys::XED_REG_GS
        | xed_sys::XED_REG_TMP0
        | xed_sys::XED_REG_TMP1
        | xed_sys::XED_REG_TMP2
        | xed_sys::XED_REG_TMP3
        | xed_sys::XED_REG_TMP4
        | xed_sys::XED_REG_TMP5
        | xed_sys::XED_REG_TMP6
        | xed_sys::XED_REG_TMP7
        | xed_sys::XED_REG_TMP8
        | xed_sys::XED_REG_TMP9
        | xed_sys::XED_REG_TMP10
        | xed_sys::XED_REG_TMP11
        | xed_sys::XED_REG_TMP12
        | xed_sys::XED_REG_TMP13
        | xed_sys::XED_REG_TMP14
        | xed_sys::XED_REG_TMP15 => {
            // We consider use of all these registers out of scope
            true
        },
        xed_sys::XED_REG_FLAGS
        | xed_sys::XED_REG_EFLAGS
        | xed_sys::XED_REG_RFLAGS
        | xed_sys::XED_REG_AX
        | xed_sys::XED_REG_CX
        | xed_sys::XED_REG_DX
        | xed_sys::XED_REG_BX
        | xed_sys::XED_REG_SP
        | xed_sys::XED_REG_BP
        | xed_sys::XED_REG_SI
        | xed_sys::XED_REG_DI
        | xed_sys::XED_REG_R8W
        | xed_sys::XED_REG_R9W
        | xed_sys::XED_REG_R10W
        | xed_sys::XED_REG_R11W
        | xed_sys::XED_REG_R12W
        | xed_sys::XED_REG_R13W
        | xed_sys::XED_REG_R14W
        | xed_sys::XED_REG_R15W
        | xed_sys::XED_REG_EAX
        | xed_sys::XED_REG_ECX
        | xed_sys::XED_REG_EDX
        | xed_sys::XED_REG_EBX
        | xed_sys::XED_REG_ESP
        | xed_sys::XED_REG_EBP
        | xed_sys::XED_REG_ESI
        | xed_sys::XED_REG_EDI
        | xed_sys::XED_REG_R8D
        | xed_sys::XED_REG_R9D
        | xed_sys::XED_REG_R10D
        | xed_sys::XED_REG_R11D
        | xed_sys::XED_REG_R12D
        | xed_sys::XED_REG_R13D
        | xed_sys::XED_REG_R14D
        | xed_sys::XED_REG_R15D
        | xed_sys::XED_REG_RAX
        | xed_sys::XED_REG_RCX
        | xed_sys::XED_REG_RDX
        | xed_sys::XED_REG_RBX
        | xed_sys::XED_REG_RSP
        | xed_sys::XED_REG_RBP
        | xed_sys::XED_REG_RSI
        | xed_sys::XED_REG_RDI
        | xed_sys::XED_REG_R8
        | xed_sys::XED_REG_R9
        | xed_sys::XED_REG_R10
        | xed_sys::XED_REG_R11
        | xed_sys::XED_REG_R12
        | xed_sys::XED_REG_R13
        | xed_sys::XED_REG_R14
        | xed_sys::XED_REG_R15
        | xed_sys::XED_REG_AL
        | xed_sys::XED_REG_CL
        | xed_sys::XED_REG_DL
        | xed_sys::XED_REG_BL
        | xed_sys::XED_REG_SPL
        | xed_sys::XED_REG_BPL
        | xed_sys::XED_REG_SIL
        | xed_sys::XED_REG_DIL
        | xed_sys::XED_REG_R8B
        | xed_sys::XED_REG_R9B
        | xed_sys::XED_REG_R10B
        | xed_sys::XED_REG_R11B
        | xed_sys::XED_REG_R12B
        | xed_sys::XED_REG_R13B
        | xed_sys::XED_REG_R14B
        | xed_sys::XED_REG_R15B
        | xed_sys::XED_REG_AH
        | xed_sys::XED_REG_CH
        | xed_sys::XED_REG_DH
        | xed_sys::XED_REG_BH
        | xed_sys::XED_REG_STACKPUSH
        | xed_sys::XED_REG_STACKPOP
        | xed_sys::XED_REG_ST0
        | xed_sys::XED_REG_ST1
        | xed_sys::XED_REG_ST2
        | xed_sys::XED_REG_ST3
        | xed_sys::XED_REG_ST4
        | xed_sys::XED_REG_ST5
        | xed_sys::XED_REG_ST6
        | xed_sys::XED_REG_ST7
        | xed_sys::XED_REG_XCR0
        | xed_sys::XED_REG_XMM0
        | xed_sys::XED_REG_XMM1
        | xed_sys::XED_REG_XMM2
        | xed_sys::XED_REG_XMM3
        | xed_sys::XED_REG_XMM4
        | xed_sys::XED_REG_XMM5
        | xed_sys::XED_REG_XMM6
        | xed_sys::XED_REG_XMM7
        | xed_sys::XED_REG_XMM8
        | xed_sys::XED_REG_XMM9
        | xed_sys::XED_REG_XMM10
        | xed_sys::XED_REG_XMM11
        | xed_sys::XED_REG_XMM12
        | xed_sys::XED_REG_XMM13
        | xed_sys::XED_REG_XMM14
        | xed_sys::XED_REG_XMM15
        | xed_sys::XED_REG_XMM16
        | xed_sys::XED_REG_XMM17
        | xed_sys::XED_REG_XMM18
        | xed_sys::XED_REG_XMM19
        | xed_sys::XED_REG_XMM20
        | xed_sys::XED_REG_XMM21
        | xed_sys::XED_REG_XMM22
        | xed_sys::XED_REG_XMM23
        | xed_sys::XED_REG_XMM24
        | xed_sys::XED_REG_XMM25
        | xed_sys::XED_REG_XMM26
        | xed_sys::XED_REG_XMM27
        | xed_sys::XED_REG_XMM28
        | xed_sys::XED_REG_XMM29
        | xed_sys::XED_REG_XMM30
        | xed_sys::XED_REG_XMM31
        | xed_sys::XED_REG_YMM0
        | xed_sys::XED_REG_YMM1
        | xed_sys::XED_REG_YMM2
        | xed_sys::XED_REG_YMM3
        | xed_sys::XED_REG_YMM4
        | xed_sys::XED_REG_YMM5
        | xed_sys::XED_REG_YMM6
        | xed_sys::XED_REG_YMM7
        | xed_sys::XED_REG_YMM8
        | xed_sys::XED_REG_YMM9
        | xed_sys::XED_REG_YMM10
        | xed_sys::XED_REG_YMM11
        | xed_sys::XED_REG_YMM12
        | xed_sys::XED_REG_YMM13
        | xed_sys::XED_REG_YMM14
        | xed_sys::XED_REG_YMM15
        | xed_sys::XED_REG_YMM16
        | xed_sys::XED_REG_YMM17
        | xed_sys::XED_REG_YMM18
        | xed_sys::XED_REG_YMM19
        | xed_sys::XED_REG_YMM20
        | xed_sys::XED_REG_YMM21
        | xed_sys::XED_REG_YMM22
        | xed_sys::XED_REG_YMM23
        | xed_sys::XED_REG_YMM24
        | xed_sys::XED_REG_YMM25
        | xed_sys::XED_REG_YMM26
        | xed_sys::XED_REG_YMM27
        | xed_sys::XED_REG_YMM28
        | xed_sys::XED_REG_YMM29
        | xed_sys::XED_REG_YMM30
        | xed_sys::XED_REG_YMM31
        | xed_sys::XED_REG_ZMM0
        | xed_sys::XED_REG_ZMM1
        | xed_sys::XED_REG_ZMM2
        | xed_sys::XED_REG_ZMM3
        | xed_sys::XED_REG_ZMM4
        | xed_sys::XED_REG_ZMM5
        | xed_sys::XED_REG_ZMM6
        | xed_sys::XED_REG_ZMM7
        | xed_sys::XED_REG_ZMM8
        | xed_sys::XED_REG_ZMM9
        | xed_sys::XED_REG_ZMM10
        | xed_sys::XED_REG_ZMM11
        | xed_sys::XED_REG_ZMM12
        | xed_sys::XED_REG_ZMM13
        | xed_sys::XED_REG_ZMM14
        | xed_sys::XED_REG_ZMM15
        | xed_sys::XED_REG_ZMM16
        | xed_sys::XED_REG_ZMM17
        | xed_sys::XED_REG_ZMM18
        | xed_sys::XED_REG_ZMM19
        | xed_sys::XED_REG_ZMM20
        | xed_sys::XED_REG_ZMM21
        | xed_sys::XED_REG_ZMM22
        | xed_sys::XED_REG_ZMM23
        | xed_sys::XED_REG_ZMM24
        | xed_sys::XED_REG_ZMM25
        | xed_sys::XED_REG_ZMM26
        | xed_sys::XED_REG_ZMM27
        | xed_sys::XED_REG_ZMM28
        | xed_sys::XED_REG_ZMM29
        | xed_sys::XED_REG_ZMM30
        | xed_sys::XED_REG_ZMM31
        | xed_sys::XED_REG_MMX0
        | xed_sys::XED_REG_MMX1
        | xed_sys::XED_REG_MMX2
        | xed_sys::XED_REG_MMX3
        | xed_sys::XED_REG_MMX4
        | xed_sys::XED_REG_MMX5
        | xed_sys::XED_REG_MMX6
        | xed_sys::XED_REG_MMX7
        | xed_sys::XED_REG_FSBASE
        | xed_sys::XED_REG_GSBASE
        | xed_sys::XED_REG_RIP
        | xed_sys::XED_REG_EIP
        | xed_sys::XED_REG_IP
        | xed_sys::XED_REG_X87CONTROL
        | xed_sys::XED_REG_X87STATUS
        | xed_sys::XED_REG_X87TAG
        | xed_sys::XED_REG_X87PUSH
        | xed_sys::XED_REG_X87POP
        | xed_sys::XED_REG_X87POP2
        | xed_sys::XED_REG_X87OPCODE
        | xed_sys::XED_REG_X87LASTCS
        | xed_sys::XED_REG_X87LASTIP
        | xed_sys::XED_REG_X87LASTDS
        | xed_sys::XED_REG_X87LASTDP => {
            // These are all general-purpose registers
            false
        },
        reg => panic!("Unknown register ID {reg:?}"),
    }
}

fn is_out_of_scope(iclass: u32) -> bool {
    matches!(
        iclass,
        // Conditional memory accesses
        xed_sys::XED_ICLASS_VPMASKMOVQ
        | xed_sys::XED_ICLASS_VPMASKMOVD
        | xed_sys::XED_ICLASS_VMASKMOVPS
        | xed_sys::XED_ICLASS_VMASKMOVPD
        | xed_sys::XED_ICLASS_VPGATHERDQ
        | xed_sys::XED_ICLASS_VPGATHERQD
        | xed_sys::XED_ICLASS_VPGATHERDD
        | xed_sys::XED_ICLASS_VPGATHERQQ
        | xed_sys::XED_ICLASS_VGATHERDPD
        | xed_sys::XED_ICLASS_VGATHERDPS
        | xed_sys::XED_ICLASS_VGATHERQPD
        | xed_sys::XED_ICLASS_VGATHERQPS
        | xed_sys::XED_ICLASS_VPBLENDW

        // Faults
        | xed_sys::XED_ICLASS_INT
        | xed_sys::XED_ICLASS_INT3
        | xed_sys::XED_ICLASS_IN
        | xed_sys::XED_ICLASS_OUT
        | xed_sys::XED_ICLASS_OUTSD
        | xed_sys::XED_ICLASS_IRETD
        | xed_sys::XED_ICLASS_IRETQ
        | xed_sys::XED_ICLASS_VMCALL
        | xed_sys::XED_ICLASS_VMMCALL
        | xed_sys::XED_ICLASS_STGI
        | xed_sys::XED_ICLASS_CLZERO
        | xed_sys::XED_ICLASS_SYSCALL
        | xed_sys::XED_ICLASS_UD0
        | xed_sys::XED_ICLASS_UD1
        | xed_sys::XED_ICLASS_UD2

        // Unsupported registers
        | xed_sys::XED_ICLASS_XGETBV

        // Segment descriptors
        | xed_sys::XED_ICLASS_CALL_FAR
        | xed_sys::XED_ICLASS_JMP_FAR
        | xed_sys::XED_ICLASS_RET_FAR
        | xed_sys::XED_ICLASS_FXSAVE
        | xed_sys::XED_ICLASS_FXSAVE64
        | xed_sys::XED_ICLASS_XSAVE
        | xed_sys::XED_ICLASS_XSAVE64
        | xed_sys::XED_ICLASS_XSAVEOPT
        | xed_sys::XED_ICLASS_XSAVEOPT64
        | xed_sys::XED_ICLASS_XSAVEC
        | xed_sys::XED_ICLASS_XSAVEC64
        | xed_sys::XED_ICLASS_XSAVES
        | xed_sys::XED_ICLASS_XSAVES64
        | xed_sys::XED_ICLASS_XRSTOR
        | xed_sys::XED_ICLASS_XRSTOR64
        | xed_sys::XED_ICLASS_XRSTORS
        | xed_sys::XED_ICLASS_XRSTORS64
        | xed_sys::XED_ICLASS_FXRSTOR
        | xed_sys::XED_ICLASS_FXRSTOR64
    )
}
