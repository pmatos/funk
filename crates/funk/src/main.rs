//! `funk`, the driver: `funk fmt` prints fir in its canonical form, and
//! `funk verify` checks it. Both report as text, or as JSON with `--json`
//! (ADR-2026-10-30-1032).

mod json;
mod report;

use std::io::{Read, Write};
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
        && let Err(e) = replace(file, &text)
    {
        report.verdict = Verdict::IoError;
        report
            .problems
            .push(Problem::Io(format!("cannot write {file}: {e}")));
    }
    (report, Some(Formatted { text, canonical }))
}

/// Replaces the contents of `file` with `text` all at once: writes a
/// temporary file next to it, with its permissions, then renames it over
/// the file, so a failed write leaves the file as it was.
fn replace(file: &str, text: &str) -> std::io::Result<()> {
    let target = std::fs::canonicalize(file)?;
    let mut tmp = target.clone().into_os_string();
    tmp.push(".funk-fmt.tmp");
    let tmp = std::path::PathBuf::from(tmp);
    let written = std::fs::write(&tmp, text)
        .and_then(|()| std::fs::set_permissions(&tmp, std::fs::metadata(&target)?.permissions()))
        .and_then(|()| std::fs::rename(&tmp, &target));
    if written.is_err() {
        let _ = std::fs::remove_file(&tmp);
    }
    written
}

fn run(args: &[String]) -> u8 {
    let a = match parse_args(args) {
        Ok(Request::Run(a)) => a,
        Ok(Request::Help) => {
            println!("{USAGE}");
            return 0;
        }
        Ok(Request::Version) => {
            println!("funk {}", env!("CARGO_PKG_VERSION"));
            return 0;
        }
        Err(why) => {
            eprintln!("funk: {why}\n\n{USAGE}");
            return 2;
        }
    };
    let reg = Registry::core();
    let mut status = 0;
    let mut stdout = std::io::stdout().lock();
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
        let out = if a.json {
            if a.mode == FmtMode::Print
                && let Some(f) = &formatted
            {
                report.extra.push(("text", Json::str(f.text.clone())));
            }
            writeln!(stdout, "{}", report.json())
        } else {
            for p in &report.problems {
                eprintln!("{}", p.text(file));
            }
            match (a.mode, formatted) {
                (FmtMode::Print, Some(f)) => stdout.write_all(f.text.as_bytes()),
                (FmtMode::Check, Some(_)) if not_canonical => writeln!(stdout, "{file}"),
                _ => Ok(()),
            }
        };
        if out.is_err() {
            return 2;
        }
    }
    status
}

fn main() -> ExitCode {
    let mut args = Vec::new();
    for arg in std::env::args_os().skip(1) {
        match arg.into_string() {
            Ok(s) => args.push(s),
            Err(bad) => {
                eprintln!("funk: argument {bad:?} is not UTF-8\n\n{USAGE}");
                return ExitCode::from(2);
            }
        }
    }
    // The parser, the printer and the verifier recurse once per level of
    // nesting of attributes, regions and items, so funk runs them on a
    // large stack. The stack is reserved, not committed; where it cannot be
    // reserved, funk runs on the main thread's stack.
    let worker_args = args.clone();
    let worker = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || run(&worker_args));
    let status = match worker {
        Ok(w) => w.join().unwrap_or(2),
        Err(_) => run(&args),
    };
    ExitCode::from(status)
}
