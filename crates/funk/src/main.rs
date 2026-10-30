//! `funk`, the driver: `funk fmt` prints fir in its canonical form, and
//! `funk verify` checks it. Both report as text, or as JSON with `--json`
//! (ADR-2026-10-30-1032).

mod json;
mod report;

use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use funk_ir::{Registry, print, text::parse_bytes, verify};
use json::Json;
use report::{Problem, Report, Verdict};

const USAGE: &str = "\
usage: funk fmt [--check | --write] [--json] FILE...
       funk verify [--json] FILE...

  fmt      Parse each FILE and print it in canonical form. fmt does not
           validate: a module that parses has a canonical form.
             --check  print the name of each FILE that is not canonical
             --write  rewrite each FILE that is not canonical in place
  verify   Parse and validate each FILE. Print nothing when all are valid.

  --json   Report one JSON object per FILE on stdout, with its verdict
           (accepted, parse-error, validation-error or io-error) and its
           diagnostics.
  FILE     A path, or - for standard input, at most once.
  -h, --help     Print this help.
  -V, --version  Print funk's version.

Exit status: 0 when every FILE is accepted (and, with --check, canonical),
1 when one is rejected or not canonical, 2 on a usage or I/O error.";

/// What `funk fmt` does with a canonical text.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FmtMode {
    Print,
    Check,
    Write,
}

/// What the command line asks for.
enum Request {
    Help,
    Version,
    Run(Args),
}

struct Args {
    command: String,
    mode: FmtMode,
    json: bool,
    files: Vec<String>,
}

fn parse_args(args: &[String]) -> Result<Request, String> {
    let mut options = args.iter().take_while(|a| *a != "--");
    if args.first().is_some_and(|a| a == "help")
        || options.clone().any(|a| a == "-h" || a == "--help")
    {
        return Ok(Request::Help);
    }
    if options.any(|a| a == "-V" || a == "--version") {
        return Ok(Request::Version);
    }
    let (command, rest) = args.split_first().ok_or("missing command")?;
    if command != "fmt" && command != "verify" {
        return Err(format!("unknown command {command}"));
    }
    let mut a = Args {
        command: command.clone(),
        mode: FmtMode::Print,
        json: false,
        files: Vec::new(),
    };
    let mut options = true;
    for arg in rest {
        match arg.as_str() {
            "--" if options => options = false,
            "--json" if options => a.json = true,
            "--check" | "--write" if options && command == "fmt" => {
                let mode = if arg == "--check" {
                    FmtMode::Check
                } else {
                    FmtMode::Write
                };
                if a.mode != FmtMode::Print && a.mode != mode {
                    return Err("--check and --write exclude each other".into());
                }
                a.mode = mode;
            }
            s if options && s.starts_with("--") => return Err(format!("unknown option {s}")),
            s => a.files.push(s.to_string()),
        }
    }
    if a.files.is_empty() {
        return Err("no FILE given; use - for standard input".into());
    }
    if a.mode == FmtMode::Write && a.files.iter().any(|f| f == "-") {
        return Err("--write cannot rewrite standard input".into());
    }
    if a.files.iter().filter(|f| *f == "-").count() > 1 {
        return Err("- may be given once: standard input can be read only once".into());
    }
    Ok(Request::Run(a))
}

fn read(file: &str) -> Result<Vec<u8>, String> {
    if file == "-" {
        let mut bytes = Vec::new();
        std::io::stdin()
            .read_to_end(&mut bytes)
            .map_err(|e| format!("cannot read standard input: {e}"))?;
        return Ok(bytes);
    }
    std::fs::read(file).map_err(|e| format!("cannot read {file}: {e}"))
}

/// The report on `file`, with no fields beyond the common ones yet.
fn file_report(file: &str, verdict: Verdict, problems: Vec<Problem>) -> Report {
    Report {
        file: file.to_string(),
        verdict,
        problems,
        extra: Vec::new(),
    }
}

fn verify_file(file: &str, reg: &Registry) -> Report {
    let bytes = match read(file) {
        Ok(b) => b,
        Err(why) => return file_report(file, Verdict::IoError, vec![Problem::Io(why)]),
    };
    match parse_bytes(&bytes, reg) {
        Err(e) => file_report(file, Verdict::ParseError, vec![Problem::Parse(e)]),
        Ok(m) => match verify(&m, reg) {
            ds if ds.is_empty() => file_report(file, Verdict::Accepted, Vec::new()),
            ds => file_report(
                file,
                Verdict::ValidationError,
                Problem::validation(ds, &m.locs),
            ),
        },
    }
}

/// The canonical text of a file that parsed, and whether the file holds it.
struct Formatted {
    text: String,
    canonical: bool,
}

/// Formats one file. Returns the report and, if the file parsed, its
/// canonical text.
fn fmt_file(file: &str, mode: FmtMode, reg: &Registry) -> (Report, Option<Formatted>) {
    let bytes = match read(file) {
        Ok(b) => b,
        Err(why) => {
            return (
                file_report(file, Verdict::IoError, vec![Problem::Io(why)]),
                None,
            );
        }
    };
    let m = match parse_bytes(&bytes, reg) {
        Ok(m) => m,
        Err(e) => {
            return (
                file_report(file, Verdict::ParseError, vec![Problem::Parse(e)]),
                None,
            );
        }
    };
    let text = print(&m);
    let canonical = text.as_bytes() == bytes.as_slice();
    let mut report = file_report(file, Verdict::Accepted, Vec::new());
    report.extra.push(("canonical", Json::Bool(canonical)));
    if mode == FmtMode::Write
        && !canonical
        && let Err(why) = replace(file, &text)
    {
        report.verdict = Verdict::IoError;
        report.problems.push(Problem::Io(why));
    }
    (report, Some(Formatted { text, canonical }))
}

/// Replaces the contents of `file` with `text` all at once: writes a new
/// temporary file next to it, gives it the file's permissions, then renames
/// it over the file, so a failed write leaves the file as it was. A file
/// that funk may not write is left alone, as is anything already at a
/// temporary name.
fn replace(file: &str, text: &str) -> Result<(), String> {
    let cannot = |e: &dyn std::fmt::Display| format!("cannot write {file}: {e}");
    let target = std::fs::canonicalize(file).map_err(|e| cannot(&e))?;
    let meta = std::fs::metadata(&target).map_err(|e| cannot(&e))?;
    if !meta.is_file() {
        return Err(cannot(&"it is not a regular file"));
    }
    OpenOptions::new()
        .write(true)
        .open(&target)
        .map_err(|e| cannot(&e))?;
    let (tmp, mut out) = create_temp(&target).map_err(|e| cannot(&e))?;
    let written = out
        .write_all(text.as_bytes())
        .and_then(|()| out.set_permissions(meta.permissions()))
        .and_then(|()| out.sync_all())
        .map_err(|e| format!("cannot write {}: {e}", tmp.display()))
        .and_then(|()| std::fs::rename(&tmp, &target).map_err(|e| cannot(&e)));
    if written.is_err() {
        let _ = std::fs::remove_file(&tmp);
    }
    written
}

/// Creates a new file next to `target`, named after it, readable only by
/// its owner. Never opens a path that exists, so a file or a link already
/// there is not touched, and concurrent runs each get their own.
fn create_temp(target: &Path) -> std::io::Result<(PathBuf, File)> {
    let dir = target.parent().unwrap_or(Path::new("."));
    let name = target.file_name().unwrap_or_default().to_string_lossy();
    let mut open = OpenOptions::new();
    open.write(true).create_new(true);
    #[cfg(unix)]
    std::os::unix::fs::OpenOptionsExt::mode(&mut open, 0o600);
    let mut n = 0u32;
    loop {
        let tmp = dir.join(format!(".{name}.funk-fmt.{n}.tmp"));
        match open.open(&tmp) {
            Ok(f) => return Ok((tmp, f)),
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists && n < 999 => n += 1,
            Err(e) => return Err(e),
        }
    }
}

/// A write to standard output or standard error that failed.
struct OutputError(&'static str, std::io::Error);

fn to_stdout(e: std::io::Error) -> OutputError {
    OutputError("standard output", e)
}

fn to_stderr(e: std::io::Error) -> OutputError {
    OutputError("standard error", e)
}

/// Runs funk and returns its exit status. When funk cannot write its
/// output, it says so on standard error if it can, and exits with 2.
fn run(args: &[String]) -> u8 {
    match run_commands(args) {
        Ok(status) => status,
        // A reader that stopped reading, as `head` does, wants no more
        // output and no message.
        Err(OutputError(_, e)) if e.kind() == std::io::ErrorKind::BrokenPipe => 2,
        Err(OutputError(what, e)) => {
            let _ = writeln!(std::io::stderr(), "funk: cannot write {what}: {e}");
            2
        }
    }
}

fn run_commands(args: &[String]) -> Result<u8, OutputError> {
    let mut stdout = std::io::stdout().lock();
    let mut stderr = std::io::stderr().lock();
    let a = match parse_args(args) {
        Ok(Request::Run(a)) => a,
        Ok(Request::Help) => {
            writeln!(stdout, "{USAGE}").map_err(to_stdout)?;
            stdout.flush().map_err(to_stdout)?;
            return Ok(0);
        }
        Ok(Request::Version) => {
            writeln!(stdout, "funk {}", env!("CARGO_PKG_VERSION")).map_err(to_stdout)?;
            stdout.flush().map_err(to_stdout)?;
            return Ok(0);
        }
        Err(why) => {
            writeln!(stderr, "funk: {why}\n\n{USAGE}").map_err(to_stderr)?;
            return Ok(2);
        }
    };
    let reg = Registry::core();
    let mut status = 0;
    for file in &a.files {
        let (mut report, formatted) = if a.command == "verify" {
            (verify_file(file, &reg), None)
        } else {
            fmt_file(file, a.mode, &reg)
        };
        let not_canonical = formatted.as_ref().is_some_and(|f| !f.canonical);
        status = status.max(match report.verdict {
            Verdict::Accepted if a.mode == FmtMode::Check && not_canonical => 1,
            Verdict::Accepted => 0,
            Verdict::ParseError | Verdict::ValidationError => 1,
            Verdict::IoError => 2,
        });
        if a.json {
            if a.mode == FmtMode::Print
                && let Some(f) = &formatted
            {
                report.extra.push(("text", Json::str(f.text.clone())));
            }
            writeln!(stdout, "{}", report.json()).map_err(to_stdout)?;
        } else {
            for p in &report.problems {
                writeln!(stderr, "{}", p.text(file)).map_err(to_stderr)?;
            }
            match (a.mode, formatted) {
                (FmtMode::Print, Some(f)) => stdout.write_all(f.text.as_bytes()),
                (FmtMode::Check, Some(_)) if not_canonical => writeln!(stdout, "{file}"),
                _ => Ok(()),
            }
            .map_err(to_stdout)?;
        }
    }
    stdout.flush().map_err(to_stdout)?;
    Ok(status)
}

fn main() -> ExitCode {
    let mut args = Vec::new();
    for arg in std::env::args_os().skip(1) {
        match arg.into_string() {
            Ok(s) => args.push(s),
            Err(bad) => {
                let _ = writeln!(
                    std::io::stderr(),
                    "funk: argument {bad:?} is not UTF-8\n\n{USAGE}"
                );
                return ExitCode::from(2);
            }
        }
    }
    ExitCode::from(run(&args))
}
