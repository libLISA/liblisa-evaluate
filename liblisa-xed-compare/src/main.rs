use std::collections::HashSet;
use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;

use clap::Parser;
use liblisa::arch::x64::X64Arch;
use liblisa::encoding::Encoding;
use liblisa::semantics::default::computation::SynthesizedComputation;
use liblisa_progress::{progress_data, Progress, ProgressUsize};
use rayon::prelude::*;

#[derive(clap::Parser)]
struct Args {
    #[clap(long)]
    encodings: PathBuf,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let args = Args::parse();
    let file = File::open(args.encodings)?;

    eprintln!("Loading encodings...");
    let encodings: Vec<Encoding<X64Arch, SynthesizedComputation>> = serde_json::from_reader(BufReader::new(file)).unwrap();

    let (mmode, stack_addr_width) = (xed_sys::XED_MACHINE_MODE_LONG_64, xed_sys::XED_ADDRESS_WIDTH_64b);
    unsafe {
        xed_sys::xed_tables_init();
    }

    let results = Progress::run(
        progress_data! {
            P {
                num_done: ProgressUsize = 0,
                num_undocumented: ProgressUsize = 0,
                total: usize = encodings.len(),
            }, |f, P { num_done, num_undocumented, total }| write!(f, "Checked {num_done} / {total} encodings: {num_undocumented} undocumented")
        },
        |p| {
            encodings
                .par_iter()
                .enumerate()
                .map(|(_encoding_index, encoding)| {
                    let _d = p.num_done.delayed_increment();
                    // eprintln!("Encoding {:02X?} ({} / {})", encoding.instr().bytes(), encoding_index, encodings.len());

                    let mut rng = rand::thread_rng();
                    let part_values = encoding.parts.iter().map(|_| None).collect::<Vec<_>>();
                    let mut seen = HashSet::new();
                    let random_instrs = encoding
                        .random_instrs(&part_values, &mut rng)
                        .take(10_000)
                        .filter(|instr| seen.insert(*instr));
                    let mut iforms = HashSet::new();
                    let mut iclasses = HashSet::new();
                    let mut undocumented = false;
                    for instance in random_instrs {
                        unsafe {
                            let itext = instance.bytes();
                            let mut xedd = ::std::mem::MaybeUninit::<xed_sys::xed_decoded_inst_t>::uninit();
                            xed_sys::xed_decoded_inst_zero(xedd.as_mut_ptr());
                            xed_sys::xed_decoded_inst_set_mode(xedd.as_mut_ptr(), mmode, stack_addr_width);

                            let xed_error: xed_sys::xed_error_enum_t =
                                xed_sys::xed_decode(xedd.as_mut_ptr(), itext.as_ptr(), itext.len() as u32);
                            let desc = std::ffi::CStr::from_ptr(xed_sys::xed_error_enum_t2str(xed_error)).to_string_lossy();
                            if xed_error != xed_sys::XED_ERROR_NONE {
                                if !undocumented {
                                    eprintln!("\nXED error={} for {:02X?} of {encoding}", desc, instance.bytes());
                                    p.num_undocumented.increment();
                                }

                                undocumented = true;
                            } else {
                                let inst = xed_sys::xed_decoded_inst_inst(xedd.as_mut_ptr());
                                let iclass = xed_sys::xed_inst_iclass(inst);
                                let iform = xed_sys::xed_inst_iform_enum(inst);

                                if iclasses.insert(iclass) {
                                    // let iclass_name = std::ffi::CStr::from_ptr(xed_sys::xed_iclass_enum_t2str(iclass)).to_string_lossy();
                                    // eprintln!("iclasses={}/{} with new {}", iclasses.len(), xed_sys::XED_ICLASS_LAST, iclass_name);
                                }

                                if iforms.insert(iform) {
                                    // let iform_name = std::ffi::CStr::from_ptr(xed_sys::xed_iform_enum_t2str(iform)).to_string_lossy();
                                    // eprintln!("iforms={}/{} with new {}", iforms.len(), xed_sys::XED_IFORM_LAST, iform_name);
                                }
                            }
                        };
                    }

                    (iclasses, iforms, undocumented)
                })
                .collect::<Vec<_>>()
        },
    );

    let mut iclasses = HashSet::new();
    let mut iforms = HashSet::new();
    let mut num_unknown = 0usize;

    for (r_iclasses, r_iforms, undocumented) in results {
        iclasses.extend(r_iclasses);
        iforms.extend(r_iforms);
        num_unknown += if undocumented { 1 } else { 0 };
    }

    let mut num_in_scope_iforms = 0;
    for iform in 0..xed_sys::XED_IFORM_LAST {
        let iform_name = unsafe { std::ffi::CStr::from_ptr(xed_sys::xed_iform_enum_t2str(iform)).to_string_lossy() };
        let is_avx = iform_name.contains("_AVX512");

        if !is_avx {
            num_in_scope_iforms += 1;
        }

        if !iforms.contains(&iform) && !is_avx {
            eprintln!("iform missing: {iform_name}");
        }
    }

    // TODO: Exclude privileged instructions
    // TODO: Exclude legacy instructions that have been removed in recent CPUs
    // TODO: Exclude 32bit-only iforms
    println!("In-scope iforms: {num_in_scope_iforms}");
    println!("Unknown encodings: {num_unknown}");
    println!("iclasses = {}", iclasses.len());
    println!("iforms = {}", iforms.len());
    println!("encodings per iform = {:.2}", encodings.len() as f64 / iforms.len() as f64);

    Ok(())
}
