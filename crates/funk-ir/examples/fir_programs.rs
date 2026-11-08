//! Writes the programs that the differential harness runs (#165): for each
//! seed, `program-SEED.fir` and its runs, `program-SEED.toml`.
//!
//! Usage: `cargo run -p funk-ir --example fir_programs -- OUT_DIR FIRST COUNT [SEED...]`
//!
//! The seeds are FIRST to FIRST + COUNT - 1, and each SEED.

use std::path::Path;
use std::process::ExitCode;

use funk_ir::generate::Rng;
use funk_ir::generate::program;
use funk_ir::print;

fn seed(s: &str) -> Result<u64, String> {
    s.parse().map_err(|_| format!("{s} is not a seed"))
}

fn write(path: &Path, text: &str) -> Result<(), String> {
    std::fs::write(path, text).map_err(|e| format!("cannot write {}: {e}", path.display()))
}

fn run(args: &[String]) -> Result<(), String> {
    let [out, first, count, extra @ ..] = args else {
        return Err("usage: fir_programs OUT_DIR FIRST COUNT [SEED...]".into());
    };
    let (first, count) = (seed(first)?, seed(count)?);
    let out = Path::new(out);
    std::fs::create_dir_all(out).map_err(|e| format!("cannot create {}: {e}", out.display()))?;
    let extra = extra
        .iter()
        .map(|s| seed(s))
        .collect::<Result<Vec<_>, _>>()?;
    for s in (first..first.saturating_add(count)).chain(extra) {
        let p = program::program(&mut Rng::new(s));
        write(&out.join(format!("program-{s}.fir")), &print(&p.module))?;
        write(&out.join(format!("program-{s}.toml")), &p.sidecar())?;
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
