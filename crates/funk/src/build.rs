//! `funk build`: compiles one file with the x86-64 backend into an object
//! file and an executable (ADR-2026-10-30-1326). `funk asm`: prints the
//! assembly of the file's functions.

use std::path::Path;

use funk_ir::{Diagnostic, Module, Registry};
use funk_x86_64::{BuildError, build, compile, object_path};

use crate::json::Json;
use crate::report::{Kind, Problem, Report, Verdict};
use crate::{file_report, load};

/// Builds `file` into the executable `output` and the object file next to
/// it. The report names both when the build succeeds.
pub fn build_file(file: &str, output: &str, reg: &Registry) -> Report {
    let m = match load(file, reg) {
        Ok(m) => m,
        Err(report) => return report,
    };
    let exe = Path::new(output);
    if file != "-" && [exe, &object_path(exe)].iter().any(|o| same_file(file, o)) {
        let why = format!("{output} would overwrite the input {file}");
        return file_report(file, Verdict::IoError, vec![Problem::Io(why)]);
    }
    match build(&m, exe) {
        Ok(outputs) => {
            let mut report = file_report(file, Verdict::Accepted, Vec::new());
            let path = |p: &Path| Json::str(p.to_string_lossy());
            report.extra.push(("object", path(&outputs.object)));
            report.extra.push(("executable", path(&outputs.executable)));
            report
        }
        Err(BuildError::Unsupported(ds)) => unsupported(file, ds, &m),
        Err(BuildError::Tool(why)) => {
            file_report(file, Verdict::ToolError, vec![Problem::Tool(why)])
        }
        Err(BuildError::Io(why)) => file_report(file, Verdict::IoError, vec![Problem::Io(why)]),
    }
}

/// Lowers `file`. Returns the report, which holds the assembly of its
/// functions as `text`, and that assembly when the file was lowered.
pub fn asm_file(file: &str, reg: &Registry) -> (Report, Option<String>) {
    let m = match load(file, reg) {
        Ok(m) => m,
        Err(report) => return (report, None),
    };
    match compile(&m) {
        Ok(program) => {
            let mut report = file_report(file, Verdict::Accepted, Vec::new());
            report.extra.push(("text", Json::str(&program.module)));
            (report, Some(program.module))
        }
        Err(ds) => (unsupported(file, ds, &m), None),
    }
}

/// The report on a module that the backend cannot lower.
fn unsupported(file: &str, ds: Vec<Diagnostic>, m: &Module) -> Report {
    file_report(
        file,
        Verdict::Unsupported,
        Problem::located(Kind::Unsupported, ds, &m.locs),
    )
}

/// Whether `input` and `output` are one file. An output that does not
/// exist yet is not the input.
fn same_file(input: &str, output: &Path) -> bool {
    match (Path::new(input).canonicalize(), output.canonicalize()) {
        (Ok(a), Ok(b)) => a == b,
        _ => false,
    }
}
