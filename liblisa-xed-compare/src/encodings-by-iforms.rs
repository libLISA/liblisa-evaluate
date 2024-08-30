use std::{fs::File, io::BufReader, path::PathBuf, collections::HashMap};
use itertools::Itertools;
use liblisa::filters::map::FilterMap;
use liblisa_semantics::computation::SynthesizedComputation;
use clap::Parser;
use liblisa::arch::x64::X64Arch;
use liblisa::encoding::Encoding;



#[global_allocator]
static GLOBAL: jemallocator::Jemalloc = jemallocator::Jemalloc;

#[derive(clap::Parser)]
struct Args {
    encodings: PathBuf,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
enum ExceptionType {
    #[default]
    None,
    Sse,
    Mmx,
    Amx,
    IntAvx,
    Avx,
    Avx512,
    IntAvx512,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
struct Grouping {
    out_of_scope_regs: bool,
    xmm_regs: bool,
    ymm_regs: bool,
    zmm_regs: bool,
    mmx_regs: bool,
    exception_type: ExceptionType,
}

unsafe fn classify_instr(instr: &xed_sys::xed_decoded_inst_s) -> Grouping {
    let mut grouping = Grouping::default();
    let xi = xed_sys::xed_decoded_inst_inst(instr);

    let exception = xed_sys::xed_inst_exception(xi);
    grouping.exception_type = match exception {
        xed_sys::XED_EXCEPTION_INVALID => ExceptionType::None,
        xed_sys::XED_EXCEPTION_AMX_E1 | xed_sys::XED_EXCEPTION_AMX_E2 | xed_sys::XED_EXCEPTION_AMX_E3 | xed_sys::XED_EXCEPTION_AMX_E4 | xed_sys::XED_EXCEPTION_AMX_E5 | xed_sys::XED_EXCEPTION_AMX_E6 => ExceptionType::Amx,
        xed_sys::XED_EXCEPTION_AVX512_E1 | xed_sys::XED_EXCEPTION_AVX512_E1NF | xed_sys::XED_EXCEPTION_AVX512_E4 | xed_sys::XED_EXCEPTION_AVX512_E4NF | xed_sys::XED_EXCEPTION_AVX512_E12 | xed_sys::XED_EXCEPTION_AVX512_E12NP | xed_sys::XED_EXCEPTION_AVX512_E5 | xed_sys::XED_EXCEPTION_AVX512_E5NF | xed_sys::XED_EXCEPTION_AVX512_E6 | xed_sys::XED_EXCEPTION_AVX512_E6NF | xed_sys::XED_EXCEPTION_AVX512_E7NM | xed_sys::XED_EXCEPTION_AVX512_E9NF => ExceptionType::IntAvx512,
        
        xed_sys::XED_EXCEPTION_AVX512_E10 | xed_sys::XED_EXCEPTION_AVX512_E10NF | xed_sys::XED_EXCEPTION_AVX512_E11 | xed_sys::XED_EXCEPTION_AVX512_E2 | xed_sys::XED_EXCEPTION_AVX512_E3 | xed_sys::XED_EXCEPTION_AVX512_E3NF | xed_sys::XED_EXCEPTION_AVX512_E7NM128 | xed_sys::XED_EXCEPTION_AVX512_K20 | xed_sys::XED_EXCEPTION_AVX512_K21 => ExceptionType::Avx512,

        xed_sys::XED_EXCEPTION_AVX_TYPE_1 | xed_sys::XED_EXCEPTION_AVX_TYPE_4 | xed_sys::XED_EXCEPTION_AVX_TYPE_4M | xed_sys::XED_EXCEPTION_AVX_TYPE_5 | xed_sys::XED_EXCEPTION_AVX_TYPE_5L | xed_sys::XED_EXCEPTION_AVX_TYPE_6 | xed_sys::XED_EXCEPTION_AVX_TYPE_7 | xed_sys::XED_EXCEPTION_AVX_TYPE_8 | xed_sys::XED_EXCEPTION_AVX_TYPE_12 => ExceptionType::IntAvx,

        xed_sys::XED_EXCEPTION_AVX_TYPE_11 | xed_sys::XED_EXCEPTION_AVX_TYPE_2 | xed_sys::XED_EXCEPTION_AVX_TYPE_2D | xed_sys::XED_EXCEPTION_AVX_TYPE_3 => ExceptionType::Avx,
        xed_sys::XED_EXCEPTION_SSE_TYPE_1 | xed_sys::XED_EXCEPTION_SSE_TYPE_2 | xed_sys::XED_EXCEPTION_SSE_TYPE_2D | xed_sys::XED_EXCEPTION_SSE_TYPE_3 | xed_sys::XED_EXCEPTION_SSE_TYPE_4 | xed_sys::XED_EXCEPTION_SSE_TYPE_4M | xed_sys::XED_EXCEPTION_SSE_TYPE_5 | xed_sys::XED_EXCEPTION_SSE_TYPE_7 => ExceptionType::Sse,
        xed_sys::XED_EXCEPTION_MMX_FP | xed_sys::XED_EXCEPTION_MMX_FP_16ALIGN | xed_sys::XED_EXCEPTION_MMX_MEM | xed_sys::XED_EXCEPTION_MMX_NOFP | xed_sys::XED_EXCEPTION_MMX_NOFP2 | xed_sys::XED_EXCEPTION_MMX_NOMEM => ExceptionType::Mmx,
        _ => unreachable!(),
    };

    for n in 0..xed_sys::xed_decoded_inst_noperands(instr) {
        let op = xed_sys::xed_inst_operand(xi, n);
        let op_name = xed_sys::xed_operand_name(op);
        if xed_sys::xed_operand_is_register(op_name) != 0 {
            match xed_sys::xed_decoded_inst_get_reg(instr, op_name) {
                xed_sys::XED_REG_INVALID | xed_sys::XED_REG_BNDCFGU | xed_sys::XED_REG_BNDSTATUS | xed_sys::XED_REG_BND0 | xed_sys::XED_REG_BND1 | xed_sys::XED_REG_BND2 | xed_sys::XED_REG_BND3 | xed_sys::XED_REG_CR0 | xed_sys::XED_REG_CR1 | xed_sys::XED_REG_CR2 | xed_sys::XED_REG_CR3 | xed_sys::XED_REG_CR4 | xed_sys::XED_REG_CR5 | xed_sys::XED_REG_CR6 | xed_sys::XED_REG_CR7 | xed_sys::XED_REG_CR8 | xed_sys::XED_REG_CR9 | xed_sys::XED_REG_CR10 | xed_sys::XED_REG_CR11 | xed_sys::XED_REG_CR12 | xed_sys::XED_REG_CR13 | xed_sys::XED_REG_CR14 | xed_sys::XED_REG_CR15 | xed_sys::XED_REG_DR0 | xed_sys::XED_REG_DR1 | xed_sys::XED_REG_DR2 | xed_sys::XED_REG_DR3 | xed_sys::XED_REG_DR4 | xed_sys::XED_REG_DR5 | xed_sys::XED_REG_DR6 | xed_sys::XED_REG_DR7 | xed_sys::XED_REG_ERROR | xed_sys::XED_REG_K0 | xed_sys::XED_REG_K1 | xed_sys::XED_REG_K2 | xed_sys::XED_REG_K3 | xed_sys::XED_REG_K4 | xed_sys::XED_REG_K5 | xed_sys::XED_REG_K6 | xed_sys::XED_REG_K7 | xed_sys::XED_REG_SSP | xed_sys::XED_REG_IA32_U_CET | xed_sys::XED_REG_MXCSR | xed_sys::XED_REG_GDTR | xed_sys::XED_REG_LDTR | xed_sys::XED_REG_IDTR | xed_sys::XED_REG_TR | xed_sys::XED_REG_TSC | xed_sys::XED_REG_TSCAUX | xed_sys::XED_REG_MSRS | xed_sys::XED_REG_ES | xed_sys::XED_REG_CS | xed_sys::XED_REG_SS | xed_sys::XED_REG_DS | xed_sys::XED_REG_FS | xed_sys::XED_REG_GS | xed_sys::XED_REG_TMP0 | xed_sys::XED_REG_TMP1 | xed_sys::XED_REG_TMP2 | xed_sys::XED_REG_TMP3 | xed_sys::XED_REG_TMP4 | xed_sys::XED_REG_TMP5 | xed_sys::XED_REG_TMP6 | xed_sys::XED_REG_TMP7 | xed_sys::XED_REG_TMP8 | xed_sys::XED_REG_TMP9 | xed_sys::XED_REG_TMP10 | xed_sys::XED_REG_TMP11 | xed_sys::XED_REG_TMP12 | xed_sys::XED_REG_TMP13 | xed_sys::XED_REG_TMP14 | xed_sys::XED_REG_TMP15                          
                => {
                    // We consider use of all these registers out of scope
                    grouping.out_of_scope_regs = true;
                }
                xed_sys::XED_REG_XMM0 | xed_sys::XED_REG_XMM1 | xed_sys::XED_REG_XMM2 | xed_sys::XED_REG_XMM3 | xed_sys::XED_REG_XMM4 | xed_sys::XED_REG_XMM5 | xed_sys::XED_REG_XMM6 | xed_sys::XED_REG_XMM7 | xed_sys::XED_REG_XMM8 | xed_sys::XED_REG_XMM9 | xed_sys::XED_REG_XMM10 | xed_sys::XED_REG_XMM11 | xed_sys::XED_REG_XMM12 | xed_sys::XED_REG_XMM13 | xed_sys::XED_REG_XMM14 | xed_sys::XED_REG_XMM15 | xed_sys::XED_REG_XMM16 | xed_sys::XED_REG_XMM17 | xed_sys::XED_REG_XMM18 | xed_sys::XED_REG_XMM19 | xed_sys::XED_REG_XMM20 | xed_sys::XED_REG_XMM21 | xed_sys::XED_REG_XMM22 | xed_sys::XED_REG_XMM23 | xed_sys::XED_REG_XMM24 | xed_sys::XED_REG_XMM25 | xed_sys::XED_REG_XMM26 | xed_sys::XED_REG_XMM27 | xed_sys::XED_REG_XMM28 | xed_sys::XED_REG_XMM29 | xed_sys::XED_REG_XMM30 | xed_sys::XED_REG_XMM31 => {
                    grouping.xmm_regs = true;
                }
                xed_sys::XED_REG_YMM0 | xed_sys::XED_REG_YMM1 | xed_sys::XED_REG_YMM2 | xed_sys::XED_REG_YMM3 | xed_sys::XED_REG_YMM4 | xed_sys::XED_REG_YMM5 | xed_sys::XED_REG_YMM6 | xed_sys::XED_REG_YMM7 | xed_sys::XED_REG_YMM8 | xed_sys::XED_REG_YMM9 | xed_sys::XED_REG_YMM10 | xed_sys::XED_REG_YMM11 | xed_sys::XED_REG_YMM12 | xed_sys::XED_REG_YMM13 | xed_sys::XED_REG_YMM14 | xed_sys::XED_REG_YMM15 | xed_sys::XED_REG_YMM16 | xed_sys::XED_REG_YMM17 | xed_sys::XED_REG_YMM18 | xed_sys::XED_REG_YMM19 | xed_sys::XED_REG_YMM20 | xed_sys::XED_REG_YMM21 | xed_sys::XED_REG_YMM22 | xed_sys::XED_REG_YMM23 | xed_sys::XED_REG_YMM24 | xed_sys::XED_REG_YMM25 | xed_sys::XED_REG_YMM26 | xed_sys::XED_REG_YMM27 | xed_sys::XED_REG_YMM28 | xed_sys::XED_REG_YMM29 | xed_sys::XED_REG_YMM30 | xed_sys::XED_REG_YMM31 => {
                    grouping.ymm_regs = true;
                }
                xed_sys::XED_REG_ZMM0 | xed_sys::XED_REG_ZMM1 | xed_sys::XED_REG_ZMM2 | xed_sys::XED_REG_ZMM3 | xed_sys::XED_REG_ZMM4 | xed_sys::XED_REG_ZMM5 | xed_sys::XED_REG_ZMM6 | xed_sys::XED_REG_ZMM7 | xed_sys::XED_REG_ZMM8 | xed_sys::XED_REG_ZMM9 | xed_sys::XED_REG_ZMM10 | xed_sys::XED_REG_ZMM11 | xed_sys::XED_REG_ZMM12 | xed_sys::XED_REG_ZMM13 | xed_sys::XED_REG_ZMM14 | xed_sys::XED_REG_ZMM15 | xed_sys::XED_REG_ZMM16 | xed_sys::XED_REG_ZMM17 | xed_sys::XED_REG_ZMM18 | xed_sys::XED_REG_ZMM19 | xed_sys::XED_REG_ZMM20 | xed_sys::XED_REG_ZMM21 | xed_sys::XED_REG_ZMM22 | xed_sys::XED_REG_ZMM23 | xed_sys::XED_REG_ZMM24 | xed_sys::XED_REG_ZMM25 | xed_sys::XED_REG_ZMM26 | xed_sys::XED_REG_ZMM27 | xed_sys::XED_REG_ZMM28 | xed_sys::XED_REG_ZMM29 | xed_sys::XED_REG_ZMM30 | xed_sys::XED_REG_ZMM31 => {
                    grouping.zmm_regs = true;
                }
                xed_sys::XED_REG_ST0 | xed_sys::XED_REG_ST1 | xed_sys::XED_REG_ST2 | xed_sys::XED_REG_ST3 | xed_sys::XED_REG_ST4 | xed_sys::XED_REG_ST5 | xed_sys::XED_REG_ST6 | xed_sys::XED_REG_ST7 | xed_sys::XED_REG_XCR0 | xed_sys::XED_REG_MMX0 | xed_sys::XED_REG_MMX1 | xed_sys::XED_REG_MMX2 | xed_sys::XED_REG_MMX3 | xed_sys::XED_REG_MMX4 | xed_sys::XED_REG_MMX5 | xed_sys::XED_REG_MMX6 | xed_sys::XED_REG_MMX7 | xed_sys::XED_REG_X87CONTROL | xed_sys::XED_REG_X87STATUS | xed_sys::XED_REG_X87TAG | xed_sys::XED_REG_X87PUSH | xed_sys::XED_REG_X87POP | xed_sys::XED_REG_X87POP2 | xed_sys::XED_REG_X87OPCODE | xed_sys::XED_REG_X87LASTCS | xed_sys::XED_REG_X87LASTIP | xed_sys::XED_REG_X87LASTDS | xed_sys::XED_REG_X87LASTDP => {
                    grouping.mmx_regs = true;
                }
                xed_sys::XED_REG_FLAGS | xed_sys::XED_REG_EFLAGS | xed_sys::XED_REG_RFLAGS | xed_sys::XED_REG_AX | xed_sys::XED_REG_CX | xed_sys::XED_REG_DX | xed_sys::XED_REG_BX | xed_sys::XED_REG_SP | xed_sys::XED_REG_BP | xed_sys::XED_REG_SI | xed_sys::XED_REG_DI | xed_sys::XED_REG_R8W | xed_sys::XED_REG_R9W | xed_sys::XED_REG_R10W | xed_sys::XED_REG_R11W | xed_sys::XED_REG_R12W | xed_sys::XED_REG_R13W | xed_sys::XED_REG_R14W | xed_sys::XED_REG_R15W | xed_sys::XED_REG_EAX | xed_sys::XED_REG_ECX | xed_sys::XED_REG_EDX | xed_sys::XED_REG_EBX | xed_sys::XED_REG_ESP | xed_sys::XED_REG_EBP | xed_sys::XED_REG_ESI | xed_sys::XED_REG_EDI | xed_sys::XED_REG_R8D | xed_sys::XED_REG_R9D | xed_sys::XED_REG_R10D | xed_sys::XED_REG_R11D | xed_sys::XED_REG_R12D | xed_sys::XED_REG_R13D | xed_sys::XED_REG_R14D | xed_sys::XED_REG_R15D | xed_sys::XED_REG_RAX | xed_sys::XED_REG_RCX | xed_sys::XED_REG_RDX | xed_sys::XED_REG_RBX | xed_sys::XED_REG_RSP | xed_sys::XED_REG_RBP | xed_sys::XED_REG_RSI | xed_sys::XED_REG_RDI | xed_sys::XED_REG_R8 | xed_sys::XED_REG_R9 | xed_sys::XED_REG_R10 | xed_sys::XED_REG_R11 | xed_sys::XED_REG_R12 | xed_sys::XED_REG_R13 | xed_sys::XED_REG_R14 | xed_sys::XED_REG_R15 | xed_sys::XED_REG_AL | xed_sys::XED_REG_CL | xed_sys::XED_REG_DL | xed_sys::XED_REG_BL | xed_sys::XED_REG_SPL | xed_sys::XED_REG_BPL | xed_sys::XED_REG_SIL | xed_sys::XED_REG_DIL | xed_sys::XED_REG_R8B | xed_sys::XED_REG_R9B | xed_sys::XED_REG_R10B | xed_sys::XED_REG_R11B | xed_sys::XED_REG_R12B | xed_sys::XED_REG_R13B | xed_sys::XED_REG_R14B | xed_sys::XED_REG_R15B | xed_sys::XED_REG_AH | xed_sys::XED_REG_CH | xed_sys::XED_REG_DH | xed_sys::XED_REG_BH | xed_sys::XED_REG_STACKPUSH | xed_sys::XED_REG_STACKPOP | xed_sys::XED_REG_FSBASE | xed_sys::XED_REG_GSBASE | xed_sys::XED_REG_RIP | xed_sys::XED_REG_EIP | xed_sys::XED_REG_IP => {
                    // These are all general-purpose registers
                }
                reg => panic!("Unknown register ID {reg:?}"),
            }
        }
    }

    grouping
}

fn main () { 
    env_logger::init();
   
    let args = Args::parse();
    let file = File::open(args.encodings).unwrap();

    println!("Loading encodings...");
    let encodings: Vec<Encoding<X64Arch, SynthesizedComputation>> = serde_json::from_reader(BufReader::new(file)).unwrap();

    println!("Processing filters...");
    let mut filters = FilterMap::new();
    for filter in encodings.iter()
        .flat_map(|e| e.filters().into_iter()) {
        filters.add(filter, ());
    }

    let (mmode, stack_addr_width) = (xed_sys::XED_MACHINE_MODE_LONG_64, xed_sys::XED_ADDRESS_WIDTH_64b);
    unsafe { xed_sys::xed_tables_init() }

    let mut mapping = HashMap::new();

    for encoding in encodings.iter() {
        let itext = encoding.instr().bytes();
        let mut xedd = ::std::mem::MaybeUninit::<xed_sys::xed_decoded_inst_t>::uninit();
        unsafe {
            xed_sys::xed_decoded_inst_zero(xedd.as_mut_ptr());
            xed_sys::xed_decoded_inst_set_mode(xedd.as_mut_ptr(), mmode, stack_addr_width);

            let xed_error: xed_sys::xed_error_enum_t = xed_sys::xed_decode(xedd.as_mut_ptr(), itext.as_ptr(), itext.len() as u32);
            let desc = std::ffi::CStr::from_ptr(xed_sys::xed_error_enum_t2str(xed_error)).to_string_lossy();
            if xed_error == xed_sys::XED_ERROR_NONE {
                let instr = xedd.assume_init();
                let inst = xed_sys::xed_decoded_inst_inst(&instr);
                let iform = xed_sys::xed_inst_iform_enum(inst);

                let grouping = classify_instr(&instr);

                mapping.entry(grouping)
                    .or_insert_with(HashMap::new)
                    .entry(iform)
                    .or_insert_with(Vec::new)
                    .push(encoding);
            } else {
                println!("error={desc} for {itext:02X?}");
            }
        }
    }

    let ordered_groupings = [
        Grouping { out_of_scope_regs: false, xmm_regs: false, ymm_regs: false, zmm_regs: false, mmx_regs: false, exception_type: ExceptionType::None },
        Grouping { out_of_scope_regs: false, xmm_regs: true, ymm_regs: false, zmm_regs: false, mmx_regs: false, exception_type: ExceptionType::None },
        Grouping { out_of_scope_regs: false, xmm_regs: false, ymm_regs: true, zmm_regs: false, mmx_regs: false, exception_type: ExceptionType::None },
        Grouping { out_of_scope_regs: false, xmm_regs: false, ymm_regs: false, zmm_regs: true, mmx_regs: false, exception_type: ExceptionType::None },
        Grouping { out_of_scope_regs: false, xmm_regs: false, ymm_regs: false, zmm_regs: false, mmx_regs: false, exception_type: ExceptionType::IntAvx },
        Grouping { out_of_scope_regs: false, xmm_regs: true, ymm_regs: false, zmm_regs: false, mmx_regs: false, exception_type: ExceptionType::IntAvx },
        Grouping { out_of_scope_regs: false, xmm_regs: false, ymm_regs: true, zmm_regs: false, mmx_regs: false, exception_type: ExceptionType::IntAvx },
        Grouping { out_of_scope_regs: false, xmm_regs: false, ymm_regs: false, zmm_regs: true, mmx_regs: false, exception_type: ExceptionType::IntAvx },
        Grouping { out_of_scope_regs: false, xmm_regs: true, ymm_regs: true, zmm_regs: false, mmx_regs: false, exception_type: ExceptionType::IntAvx },
        Grouping { out_of_scope_regs: false, xmm_regs: false, ymm_regs: false, zmm_regs: false, mmx_regs: false, exception_type: ExceptionType::IntAvx512 },
        Grouping { out_of_scope_regs: false, xmm_regs: true, ymm_regs: false, zmm_regs: false, mmx_regs: false, exception_type: ExceptionType::IntAvx512 },
        Grouping { out_of_scope_regs: false, xmm_regs: false, ymm_regs: true, zmm_regs: false, mmx_regs: false, exception_type: ExceptionType::IntAvx512 },
        Grouping { out_of_scope_regs: false, xmm_regs: false, ymm_regs: false, zmm_regs: true, mmx_regs: false, exception_type: ExceptionType::IntAvx512 },
        Grouping { out_of_scope_regs: false, xmm_regs: false, ymm_regs: false, zmm_regs: false, mmx_regs: true, exception_type: ExceptionType::Mmx },
    ];

    for grouping in ordered_groupings {
        if let Some(items) = mapping.remove(&grouping) {
            print_grouping(grouping, items);
        }
    }

    println!();
    println!();
    println!();
    println!("Remaining groupings:");

    for (grouping, items) in mapping {
        print_grouping(grouping, items);
    }
}

fn print_grouping(grouping: Grouping, items: HashMap<u32, Vec<&Encoding<liblisa::arch::x64::X64ArchImpl<liblisa::arch::x64::InScope>, SynthesizedComputation>>>) {
    println!();
    println!();
    println!("For {grouping:?}:");
    for (iform, encodings) in items {
        let iform_name = unsafe {
            std::ffi::CStr::from_ptr(xed_sys::xed_iform_enum_t2str(iform)).to_string_lossy()
        };

        println!("  - {iform_name:40}: {:X}", encodings.iter().map(|e| e.instr()).format(", "));
    }
}