use std::{collections::{HashMap, HashSet}, error::Error, fs::File, io::{BufReader, BufWriter}, path::PathBuf, sync::{atomic::{AtomicUsize, Ordering}, mpsc::{RecvTimeoutError, Sender, channel}}, time::{Duration, Instant}};
use clap::Parser;
use liblisa::{arch::{x64::PrefixScope, Scope}, instr::{FilterList, Instruction, InstructionCounter}};
use liblisa_enc::Validity;
use liblisa::arch::x64::X64Arch;
use liblisa_x64_observer::with_oracle;
use log::trace;
use rand::Rng;

#[derive(Default)]
struct FixedLenCache<const LEN: usize> {
    too_short: HashSet<[u8; LEN]>,
    too_long: HashSet<[u8; LEN]>,
    invalid: HashSet<[u8; LEN]>,
    excluded: HashSet<[u8; LEN]>,
    ok: HashSet<[u8; LEN]>,
}

impl<const LEN: usize> FixedLenCache<LEN> {
    pub fn get_or_insert_with(&mut self, key: Instruction, f: impl FnOnce() -> Validity) -> Validity {
        let bytes = into_bytes::<LEN>(key);
        if self.too_short.contains(&bytes) {
            Validity::TooShort
        } else if self.too_long.contains(&bytes) {
            Validity::TooLong
        } else if self.invalid.contains(&bytes) {
            Validity::InvalidInstruction
        } else if self.excluded.contains(&bytes) {
            Validity::Excluded
        } else if self.ok.contains(&bytes) {
            Validity::Ok
        } else {
            let validity = f();
            match validity {
                Validity::TooShort => self.too_short.insert(bytes),
                Validity::TooLong => self.too_long.insert(bytes),
                Validity::InvalidInstruction => self.invalid.insert(bytes),
                Validity::Excluded | Validity::Error => self.excluded.insert(bytes),
                Validity::Ok => self.ok.insert(bytes),
            };

            validity
        }
    }
}

#[derive(Default)]
struct Cache {
    l1: FixedLenCache<1>,
    l2: FixedLenCache<2>,
    l3: FixedLenCache<3>,
    l4: FixedLenCache<4>,
    l5: FixedLenCache<5>,
    l6: FixedLenCache<6>,
    l7: FixedLenCache<7>,
    l8: FixedLenCache<8>,
    l9: FixedLenCache<9>,
    l10: FixedLenCache<10>,
    l11: FixedLenCache<11>,
    l12: FixedLenCache<12>,
    l13: FixedLenCache<13>,
    l14: FixedLenCache<14>,
    l15: FixedLenCache<15>,
}

fn into_bytes<const NUM: usize>(instr: Instruction) -> [u8; NUM] {
    let mut bytes = [0u8; NUM];
    bytes.copy_from_slice(instr.bytes());

    bytes
}

impl Cache {
    pub fn get_or_insert_with(&mut self, key: Instruction, f: impl FnOnce() -> Validity) -> Validity {
        match key.byte_len() {
            1 => self.l1.get_or_insert_with(key, f),
            2 => self.l2.get_or_insert_with(key, f),
            3 => self.l3.get_or_insert_with(key, f),
            4 => self.l4.get_or_insert_with(key, f),
            5 => self.l5.get_or_insert_with(key, f),
            6 => self.l6.get_or_insert_with(key, f),
            7 => self.l7.get_or_insert_with(key, f),
            8 => self.l8.get_or_insert_with(key, f),
            9 => self.l9.get_or_insert_with(key, f),
            10 => self.l10.get_or_insert_with(key, f),
            11 => self.l11.get_or_insert_with(key, f),
            12 => self.l12.get_or_insert_with(key, f),
            13 => self.l13.get_or_insert_with(key, f),
            14 => self.l14.get_or_insert_with(key, f),
            15 => self.l15.get_or_insert_with(key, f),
            _ => unreachable!(),
        }
    }
}

fn smallize(instr: &Instruction) -> u128 {
    assert!(instr.byte_len() < 15);
    let mut bytes = [0u8; 16];
    bytes[..instr.byte_len()].copy_from_slice(instr.bytes());
    bytes[15] = instr.byte_len() as u8;
    u128::from_le_bytes(bytes)
}

fn run_worker(index: usize, ch: Sender<(usize, Instruction)>) -> Result<(), Box<dyn Error>> {
    with_oracle(|mut o| {
        let mut buf = [0u8; 16];
        let mut rng = rand::thread_rng();
        let mut cache = Cache::default();
        let mut found = HashSet::new();
        let filters = FilterList::new();
        for _ in 0..=1_000_000_000/5 {
            rng.fill(&mut buf);

            // Force first nibble to prevent overlaping random instructions between the threads
            buf[0] = 0xc4;
            buf[1] = (buf[1] & 0xf) | ((index as u8) << 4);
            
            for guessed_len in 1..16 {
                let instr = Instruction::new(&buf[0..guessed_len]);
                
                match cache.get_or_insert_with(instr, || Validity::infer::<X64Arch, _>(&mut o, &instr)) {
                    Validity::TooShort => (),
                    Validity::TooLong => panic!("{instr:X} is too long!"),
                    Validity::InvalidInstruction | Validity::Excluded | Validity::Error => break,
                    Validity::Ok => {
                        let mut c = InstructionCounter::range(&instr, None);
                        let mut last_instr = instr;
                        while c.tunnel_next(&filters, 0) {
                            match cache.get_or_insert_with(c.current(), || Validity::infer::<X64Arch, _>(&mut o, &c.current())) {
                                Validity::Ok => {
                                    last_instr = c.current();
                                },
                                _ => break,
                            }
                        }

                        if !found.contains(&last_instr) {
                            found.insert(last_instr);
                            ch.send((index, last_instr))?;
                        }
                        break
                    }
                }
            }
        }

        Ok(())
    })
}

#[derive(clap::Parser)]
struct Args {
    #[clap(long = "continue")]
    continue_path: Option<PathBuf>,

    output: PathBuf,
}

pub fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();
    let threads = 16;

    let mut found: Vec<_> = args.continue_path.map(|path| {
        serde_json::from_reader(BufReader::new(File::open(path).unwrap())).unwrap()
    }).unwrap_or_default();

    found.retain(|instr: &Instruction| {
        PrefixScope.is_instr_in_scope(instr.bytes())
    });

    println!("Verifying {} existing instructions", found.len());
    with_oracle(|mut o| {
        let mut cache = HashMap::new();
        found.retain(|current: &Instruction| {
            for guessed_len in 1..=current.byte_len() {
                let instr = Instruction::new(&current.bytes()[..guessed_len]);
                let result = cache.entry(smallize(&instr))
                    .or_insert_with(|| Validity::infer::<X64Arch, _>(&mut o, &instr));
                match result {
                    Validity::TooShort => (),
                    Validity::TooLong => (),
                    Validity::InvalidInstruction | Validity::Excluded | Validity::Error => return false,
                    Validity::Ok => {
                        return guessed_len == current.byte_len();
                    }
                }
            }

            false
        });
    });

    println!("{} instructions remain", found.len());

    let start = Instant::now();
    let (sender, receiver) = channel();
    let threads_running = Box::leak(Box::new(AtomicUsize::new(0))) as &AtomicUsize;
    let threads = (0..threads).map(|index| {
        let sender = sender.clone();

        std::thread::Builder::new()
            .name(format!("Worker #{index}"))
            .spawn(move || {
                let n = threads_running.fetch_add(1, Ordering::SeqCst);
                println!("[{index:02}] Workers started: {n}");
                run_worker(index, sender).unwrap();
                let n = threads_running.fetch_sub(1, Ordering::SeqCst);
                println!("[{:02}] Workers remaining: {}", index, n.saturating_sub(1));
            })
            .expect("Unable to start worker thread")
    }).collect::<Vec<_>>();

    let mut last_save = Instant::now();
    let mut new = 0usize;
    loop {
        let loop_start = Instant::now();
        loop {
            match receiver.recv_timeout(Duration::from_secs(1)) {
                Ok((_index, instr)) => {
                    if !found.contains(&instr) {
                        found.push(instr);
                        trace!("[{:02}] Found: {:02X?} (total is now {})", _index, instr.bytes(), found.len());
                        new += 1;
                    }
                },
                Err(RecvTimeoutError::Timeout) => break,
                Err(RecvTimeoutError::Disconnected) => break,
            }

            if Instant::now() - loop_start > Duration::from_secs(30) {
                break
            }
        }

        let seconds_running = (Instant::now() - start).as_secs();
        println!("Found {:.2}k instructions in {}h {}m {}s (~{:.1}k/hour) -- with {} threads", new as f64 / 1000., seconds_running / 3600, (seconds_running / 60) % 60, seconds_running % 60, (new as f64 / 1000.) / (seconds_running as f64 / (3600.0)), threads.len());

        if Instant::now() - last_save > Duration::from_secs(60 * 5) {
            last_save = Instant::now();
            found.sort();
            found.dedup();
            println!("Saving progress @ {} instructions", found.len());
            let mut tmp = args.output.clone();
            tmp.set_extension("tmp");
            serde_json::to_writer(BufWriter::new(File::create(&tmp)?), &found)?;
            std::fs::rename(&tmp, &args.output).unwrap();
            println!("Save complete");
        }

        if threads_running.load(Ordering::SeqCst) == 0 {
            break;
        }
    }

    println!("Waiting for all threads to finish...");
    let _ = threads.into_iter().map(|t| t.join()).collect::<Vec<_>>();

    found.sort();
    found.dedup();

    for instr in found.iter() {
        println!("Instruction: {instr:X}");
    }

    println!("Final number of instructions found: {}", found.len());

    serde_json::to_writer(File::create(&args.output)?, &found)?;

    Ok(())
}