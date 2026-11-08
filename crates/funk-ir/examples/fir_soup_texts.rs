//! Writes random texts for `fir-ref fmt` (#165): `COUNT` files, from seeds
//! FIRST on, each tokens of fir in any order or random bytes.
//!
//! Usage: `cargo run -p funk-ir --example fir_soup_texts -- OUT_DIR FIRST COUNT`

use std::path::Path;
use std::process::ExitCode;

use funk_ir::generate::{Rng, soup};

fn seed(s: &str) -> Result<u64, String> {
    s.parse().map_err(|_| format!("{s} is not a number"))
}

fn run(args: &[String]) -> Result<(), String> {
    let [out, first, count] = args else {
        return Err("usage: fir_soup_texts OUT_DIR FIRST COUNT".into());
    };
    let (first, count) = (seed(first)?, seed(count)?);
    let out = Path::new(out);
    std::fs::create_dir_all(out).map_err(|e| format!("cannot create {}: {e}", out.display()))?;
    for s in first..first.saturating_add(count) {
        let mut rng = Rng::new(s);
        let bytes = if rng.one_in(2) {
            soup::token_soup(&mut rng).into_bytes()
        } else {
            soup::random_bytes(&mut rng)
        };
        let path = out.join(format!("soup-{s}.fir"));
        std::fs::write(&path, bytes)
            .map_err(|e| format!("cannot write {}: {e}", path.display()))?;
    }
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("fir_soup_texts: {e}");
            ExitCode::FAILURE
        }
    }
}
