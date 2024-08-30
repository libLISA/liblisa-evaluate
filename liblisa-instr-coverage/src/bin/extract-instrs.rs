use std::{collections::HashMap, fs::File, io::BufWriter, path::PathBuf};
use clap::Parser;
use elf::{abi::SHF_ALLOC, endian::AnyEndian, section::SectionHeader, ElfBytes};
use liblisa::Instruction;

#[derive(clap::Parser)]
struct Args {
    binary_path: PathBuf,

    #[clap(long = "out")]
    outfile: PathBuf,
}

fn instr_len(itext: &[u8]) -> Option<usize> {
    let (mmode, stack_addr_width) = (xed_sys::XED_MACHINE_MODE_LONG_64, xed_sys::XED_ADDRESS_WIDTH_64b);
    unsafe {
        let mut xedd = ::std::mem::MaybeUninit::<xed_sys::xed_decoded_inst_t>::uninit();
        xed_sys::xed_decoded_inst_zero(xedd.as_mut_ptr());
        xed_sys::xed_decoded_inst_set_mode(xedd.as_mut_ptr(), mmode, stack_addr_width);

        let xed_error: xed_sys::xed_error_enum_t = xed_sys::xed_decode(xedd.as_mut_ptr(), itext.as_ptr(), itext.len() as u32);
        if xed_error == xed_sys::XED_ERROR_NONE {
            Some(xed_sys::xed_decoded_inst_get_length(&xedd.assume_init()) as usize)
        } else {
            None
        }
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    unsafe {
        xed_sys::xed_tables_init();
    }

    let args = Args::parse();
    let file_data = std::fs::read(args.binary_path) 
        .expect("Unable to open binary file");
    let file = ElfBytes::<AnyEndian>::minimal_parse(&file_data).expect("Unable to parse ELF");
    let mut instructions = Vec::new();

    let (shdrs_opt, strtab_opt) = file
        .section_headers_with_strtab()
        .expect("shdrs offsets should be valid");
    let (shdrs, strtab) = (
        shdrs_opt.expect("Should have shdrs"),
        strtab_opt.expect("Should have strtab")
    );
    let with_names: HashMap<&str, SectionHeader> = shdrs
        .iter()
        .map(|shdr| {
            (
                strtab.get(shdr.sh_name as usize).expect("Failed to get section name"),
                shdr,
            )
        })
        .collect();

    let shdr = &with_names[".text"];
    let (data, _) = file.section_data(shdr).unwrap();
    if shdr.sh_flags as u32 & SHF_ALLOC != 0 {
        println!("Section {} @ {:X}..{:X}, size = {}, actual size = {}", strtab.get(shdr.sh_name as usize).unwrap(), shdr.sh_addr, shdr.sh_addr + shdr.sh_size, shdr.sh_size, data.len());

        let mut asm = data;
        while !asm.is_empty() {
            let bytes = &asm[0..asm.len().min(16)];
            let len = instr_len(bytes);
            if let Some(len) = len {
                let instr_bytes = &bytes[..len];
                instructions.push(Instruction::new(instr_bytes));
                
                // println!("Instruction: {instr_bytes:02X?}");

                asm = &asm[len..];
            } else {
                println!("Unknown instruction: {bytes:02X?}");
                break
            }
        }
    }

    println!("Saving {} instructions to {}", instructions.len(), args.outfile.display());
    serde_json::to_writer(BufWriter::new(File::create(args.outfile)?), &instructions)?;

    Ok(())
}

fn main () { 
    env_logger::init();
    run().unwrap() 
}