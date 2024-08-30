use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::Relaxed;

use clap::Parser;
use liblisa::arch::undef::UndefinedOutputs;
use liblisa::arch::x64::undef::IntelUndefWithXed;
use liblisa::arch::x64::X64Arch;
use liblisa::encoding::Encoding;
use liblisa::semantics::default::computation::SynthesizedComputation;
use liblisa_progress::{progress_data, Progress};
use log::info;
use rayon::prelude::*;
use itertools::Itertools;

#[derive(clap::Parser)]
struct Args {
    #[clap(long)]
    encodings: PathBuf,
}

fn main() {
    env_logger::init();
    let args = Args::parse();

    println!("Loading encodings...");
    let encodings: Vec<Encoding<X64Arch, SynthesizedComputation>> =
        serde_json::from_reader(BufReader::new(File::open(args.encodings).unwrap())).unwrap();

    Progress::run(
        progress_data! {
            P {
                num_processed: AtomicUsize = AtomicUsize::new(0),
                num_undef: AtomicUsize = AtomicUsize::new(0),
                num_undef_with_semantics: AtomicUsize = AtomicUsize::new(0),
                num_encodings: usize = encodings.len(),
            }, |f, P { num_processed, num_undef, num_undef_with_semantics, num_encodings }| write!(f, "Checking encodings {num_processed:?} / {num_encodings:?} -- {num_undef_with_semantics:?} / {num_undef:?} encodings with UB have semantics")
        },
        |p| {
            encodings.par_iter().for_each(|encoding| {
                info!("Encoding {:02X?}", encoding.instr().bytes());

                let mut any_undef = false;
                for instr in encoding.iter_instrs(
                    &encoding
                        .parts
                        .iter()
                        .map(|p| if p.size() <= 4 { None } else { Some(p.value) })
                        .collect::<Vec<_>>(),
                    false
                ) {
                    if let Ok(undef) = UndefinedOutputs::of(instr.bytes(), &IntelUndefWithXed) {
                        if !undef.is_empty() {
                            any_undef = true;
                        }
                    }
                }

                p.num_processed.fetch_add(1, Relaxed);
                if any_undef {
                    p.num_undef.fetch_add(1, Relaxed);

                    if encoding.all_outputs_have_computations() {
                        p.num_undef_with_semantics.fetch_add(1, Relaxed);
                    }
                }
            })
        },
    );
}
