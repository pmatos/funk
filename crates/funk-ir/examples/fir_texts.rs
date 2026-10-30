//! Writes the texts that Rust prints for the cross-language round trip
//! (#10): the printed form of every file of the shared corpus,
//! `tests/fir/`, and of the first `COUNT` modules of the generator. The Lean
//! side parses and reprints each one, and the bytes must match
//! (`scripts/check-fir-ref.sh round-trip`).
//!
//! Usage: `cargo run -p funk-ir --example fir_texts -- OUT_DIR [COUNT]`

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use funk_ir::generate::{self, Rng};
use funk_ir::{Registry, parse, print};

/// As many modules as the Rust round-trip tests check.
const DEFAULT_COUNT: u64 = 600;

fn write(out: &Path, name: &str, text: &str) -> Result<(), String> {
    let path = out.join(name);
    std::fs::write(&path, text).map_err(|e| format!("cannot write {}: {e}", path.display()))
}

/// Prints each `.fir` file of `tests/fir/<dir>` into `out`.
fn corpus(out: &Path, dir: &str, reg: &Registry) -> Result<usize, String> {
    let src = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fir")
        .join(dir);
    let entries =
        std::fs::read_dir(&src).map_err(|e| format!("cannot read {}: {e}", src.display()))?;
    let mut count = 0;
    for entry in entries {
        let path = entry.map_err(|e| e.to_string())?.path();
        if path.extension().is_none_or(|x| x != "fir") {
            continue;
        }
        let text = std::fs::read_to_string(&path)
            .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
        let m = parse(&text, reg).map_err(|e| format!("{}:{e}", path.display()))?;
        let name = path.file_name().unwrap_or_default().to_string_lossy();
        write(out, &format!("{dir}-{name}"), &print(&m))?;
        count += 1;
    }
    Ok(count)
}

fn run(args: &[String]) -> Result<(), String> {
    let [out, rest @ ..] = args else {
        return Err("usage: fir_texts OUT_DIR [COUNT]".into());
    };
    let count = match rest {
        [] => DEFAULT_COUNT,
        [n] => n
            .parse()
            .map_err(|_| format!("COUNT is a number, not {n}"))?,
        _ => return Err("usage: fir_texts OUT_DIR [COUNT]".into()),
    };
    let out = Path::new(out);
    std::fs::create_dir_all(out).map_err(|e| format!("cannot create {}: {e}", out.display()))?;
    let reg = Registry::core();
    let files = corpus(out, "canonical", &reg)? + corpus(out, "noncanonical", &reg)?;
    for seed in 0..count {
        let m = generate::module(&mut Rng::new(seed));
        write(out, &format!("generated-{seed}.fir"), &print(&m))?;
    }
    eprintln!(
        "wrote {files} corpus texts and {count} generated modules to {}",
        out.display()
    );
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("fir_texts: {e}");
            ExitCode::FAILURE
        }
    }
}
