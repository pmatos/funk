//! Writes what the differential harness runs (#165): for each seed,
//! `programs/program-SEED.fir` and its runs, `programs/program-SEED.toml`,
//! and a random text for `fir-ref fmt`, `texts/soup-SEED.fir`.
//!
//! Usage: `cargo run -p funk-ir --example fir_programs -- OUT_DIR FIRST COUNT [SEED...]`
//!
//! The seeds are FIRST to FIRST + COUNT - 1, and each SEED.

use std::path::Path;
use std::process::ExitCode;

use funk_ir::generate::{Rng, program, soup};
use funk_ir::print;

fn seed(s: &str) -> Result<u64, String> {
    s.parse().map_err(|_| format!("{s} is not a seed"))
}

fn write(path: &Path, bytes: &[u8]) -> Result<(), String> {
    std::fs::write(path, bytes).map_err(|e| format!("cannot write {}: {e}", path.display()))
}

fn create(dir: &Path) -> Result<(), String> {
    std::fs::create_dir_all(dir).map_err(|e| format!("cannot create {}: {e}", dir.display()))
}

fn run(args: &[String]) -> Result<(), String> {
    let [out, first, count, extra @ ..] = args else {
        return Err("usage: fir_programs OUT_DIR FIRST COUNT [SEED...]".into());
    };
    let (first, count) = (seed(first)?, seed(count)?);
    let extra = extra
        .iter()
        .map(|s| seed(s))
        .collect::<Result<Vec<_>, _>>()?;
    let (programs, texts) = (
        Path::new(out).join("programs"),
        Path::new(out).join("texts"),
    );
    create(&programs)?;
    create(&texts)?;
    for s in (first..first.saturating_add(count)).chain(extra) {
        let p = program::program(&mut Rng::new(s));
        let fir = programs.join(format!("program-{s}.fir"));
        write(&fir, print(&p.module).as_bytes())?;
        write(&fir.with_extension("toml"), p.sidecar().as_bytes())?;
        let mut rng = Rng::new(s);
        let text = if rng.one_in(2) {
            soup::token_soup(&mut rng).into_bytes()
        } else {
            soup::random_bytes(&mut rng)
        };
        write(&texts.join(format!("soup-{s}.fir")), &text)?;
    }
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("fir_programs: {e}");
            ExitCode::FAILURE
        }
    }
}
