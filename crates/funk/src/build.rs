//! `funk build`: compiles one file with the x86-64 backend into an object
//! file and an executable (ADR-2026-10-30-1233).

use funk_ir::Registry;
use funk_x86_64::{BuildError, build};

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
    match build(&m, output.as_ref()) {
        Ok(outputs) => {
            let mut report = file_report(file, Verdict::Accepted, Vec::new());
            let path = |p: &std::path::Path| Json::str(p.to_string_lossy());
            report.extra.push(("object", path(&outputs.object)));
            report.extra.push(("executable", path(&outputs.executable)));
            report
        }
        Err(BuildError::Unsupported(ds)) => file_report(
            file,
            Verdict::Unsupported,
            Problem::located(Kind::Unsupported, ds, &m.locs),
        ),
        Err(BuildError::Tool(why)) => {
            file_report(file, Verdict::ToolError, vec![Problem::Tool(why)])
        }
    }
}
