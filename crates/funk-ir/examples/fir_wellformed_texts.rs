//! Writes the texts that Rust prints for the cross-language round trip over
//! well-formed modules (#146): the first `COUNT` modules of
//! `generate::wellformed` that hold only core ops, which validation mostly
//! rejects. `fir-ref fmt` parses and reprints each one without validating
//! it, and the bytes must match (`scripts/check-fir-ref.sh round-trip`).
//!
//! Usage: `cargo run -p funk-ir --example fir_wellformed_texts -- OUT_DIR [COUNT]`

use std::path::Path;
use std::process::ExitCode;

use funk_ir::generate::Rng;
use funk_ir::generate::wellformed::{self, Dialects, WELL_FORMED_MODULES};
use funk_ir::print;

fn run(args: &[String]) -> Result<(), String> {
    let usage = || "usage: fir_wellformed_texts OUT_DIR [COUNT]".to_string();
    let (out, count) = match args {
        [out] => (out, WELL_FORMED_MODULES),
        [out, n] => (
            out,
            n.parse()
                .map_err(|_| format!("COUNT is a number, not {n}"))?,
        ),
        _ => return Err(usage()),
    };
    let out = Path::new(out);
    std::fs::create_dir_all(out).map_err(|e| format!("cannot create {}: {e}", out.display()))?;
    for seed in 0..count {
        let m = wellformed::module(&mut Rng::new(seed), Dialects::Core);
        let path = out.join(format!("wellformed-{seed}.fir"));
        std::fs::write(&path, print(&m))
            .map_err(|e| format!("cannot write {}: {e}", path.display()))?;
    }
    eprintln!(
        "wrote {count} well-formed generated modules to {}",
        out.display()
    );
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("fir_wellformed_texts: {e}");
            ExitCode::FAILURE
        }
    }
}
