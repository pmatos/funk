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
  FILE     A path, or - for standard input.

Exit status: 0 when every FILE is accepted (and, with --check, canonical),
1 when one is rejected or not canonical, 2 on a usage or I/O error.";

/// What `funk fmt` does with a canonical text.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FmtMode {
    Print,
    Check,
    Write,
}

struct Args {
    command: String,
    mode: FmtMode,
    json: bool,
    files: Vec<String>,
}

fn parse_args(args: &[String]) -> Result<Args, String> {
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
    Ok(a)
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

fn rejected(file: &str, verdict: Verdict, problems: Vec<Problem>) -> Report {
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
        Err(why) => return rejected(file, Verdict::IoError, vec![Problem::Io(why)]),
    };
    match parse_bytes(&bytes, reg) {
        Err(e) => rejected(file, Verdict::ParseError, vec![Problem::Parse(e)]),
        Ok(m) => match verify(&m, reg) {
            ds if ds.is_empty() => rejected(file, Verdict::Accepted, Vec::new()),
            ds => rejected(
                file,
                Verdict::ValidationError,
                Problem::validation(ds, &m.locs),
            ),
        },
    }
}

/// Formats one file. Returns the report and the canonical text, if any.
fn fmt_file(file: &str, mode: FmtMode, reg: &Registry) -> (Report, Option<String>) {
    let bytes = match read(file) {
        Ok(b) => b,
        Err(why) => {
            return (
                rejected(file, Verdict::IoError, vec![Problem::Io(why)]),
                None,
            );
        }
    };
    let m = match parse_bytes(&bytes, reg) {
        Ok(m) => m,
        Err(e) => {
            return (
                rejected(file, Verdict::ParseError, vec![Problem::Parse(e)]),
                None,
            );
        }
    };
    let text = print(&m);
    let canonical = text.as_bytes() == bytes.as_slice();
    let mut report = rejected(file, Verdict::Accepted, Vec::new());
    report.extra.push(("canonical", Json::Bool(canonical)));
    if mode == FmtMode::Write
        && !canonical
        && let Err(e) = std::fs::write(file, &text)
    {
        report.verdict = Verdict::IoError;
        report
            .problems
            .push(Problem::Io(format!("cannot write {file}: {e}")));
    }
    (report, Some(text))
}

fn run(args: &[String]) -> u8 {
    let a = match parse_args(args) {
        Ok(a) => a,
        Err(why) => {
            eprintln!("funk: {why}\n\n{USAGE}");
            return 2;
        }
    };
    let reg = Registry::core();
    let mut status = 0;
    let mut stdout = std::io::stdout().lock();
    for file in &a.files {
        let (mut report, text) = if a.command == "verify" {
            (verify_file(file, &reg), None)
        } else {
            fmt_file(file, a.mode, &reg)
        };
        let not_canonical = report.extra.contains(&("canonical", Json::Bool(false)));
        status = status.max(match report.verdict {
            Verdict::Accepted if a.mode == FmtMode::Check && not_canonical => 1,
            Verdict::Accepted => 0,
            Verdict::ParseError | Verdict::ValidationError => 1,
            Verdict::IoError => 2,
        });
        let out = if a.json {
            if a.mode == FmtMode::Print
                && let Some(t) = &text
            {
                report.extra.push(("text", Json::str(t.clone())));
            }
            writeln!(stdout, "{}", report.json())
        } else {
            for p in &report.problems {
                eprintln!("{}", p.text(file));
            }
            match (a.mode, text) {
                (FmtMode::Print, Some(t)) => stdout.write_all(t.as_bytes()),
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
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("-h" | "--help" | "help") => {
            println!("{USAGE}");
            return ExitCode::SUCCESS;
        }
        Some("-V" | "--version") => {
            println!("funk {}", env!("CARGO_PKG_VERSION"));
            return ExitCode::SUCCESS;
        }
        _ => {}
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
