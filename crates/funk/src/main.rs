//! `funk`, the driver: `funk fmt` prints fir in its canonical form,
//! `funk verify` checks it, `funk asm` prints the x86-64 assembly of its
//! functions, and `funk build` compiles it to x86-64. Each reports as text,
//! or as JSON with `--json` (`docs/decisions/rust-ir-and-tools-funk.md`).

mod build;
mod canonical;
mod json;
mod report;
mod streams;

use std::fmt::Display;
use std::fs::{File, OpenOptions, Permissions};
use std::io::{self, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use canonical::{JsonText, Printed, is_canonical};
use funk_ir::{Module, Registry, text::parse_bytes, verify};
use json::Json;
use report::{Kind, Problem, Report, Verdict};

const USAGE: &str = "\
usage: funk fmt [--check | --write] [--json] FILE...
       funk verify [--json] FILE...
       funk build [--json] -o OUTPUT FILE
       funk asm [--json] FILE

  fmt      Parse each FILE and print it in canonical form. fmt does not
           validate: a module that parses has a canonical form.
             --check  print the name of each FILE that is not canonical
             --write  rewrite each FILE that is not canonical in place
  verify   Parse and validate each FILE. Print nothing when all are valid.
  build    Parse, validate and compile FILE for x86-64 Linux. Write the
           object file OUTPUT.o and the executable OUTPUT, which runs one
           function: OUTPUT @FUNCTION ARG... prints {\"values\":[...]}.
             -o OUTPUT  the executable to write
  asm      Parse, validate and lower FILE for x86-64 Linux, and print the
           assembly of its functions. With --json, the report holds it
           as \"text\".

  --json   Report one JSON object per FILE on stdout, with its verdict
           (accepted, parse-error, validation-error, unsupported,
           tool-error or io-error) and its diagnostics.
  FILE     A path, or - for standard input, at most once.
  -h, --help     Print this help.
  -V, --version  Print funk's version.

Exit status: 0 when every FILE is accepted (and, with --check, canonical,
or with build or asm, lowered), 1 when one is rejected, not canonical or
unsupported, 2 on a usage, I/O, assembler or linker error.";

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
    output: Option<String>,
    files: Vec<String>,
}

/// The arguments before `--` that may be flags: every one but the value of
/// `build`'s `-o`, which is a path even when it reads as a flag.
fn flags(args: &[String]) -> Vec<&str> {
    let build = args.first().is_some_and(|a| a == "build");
    let mut out = Vec::new();
    let mut walk = args.iter();
    while let Some(a) = walk.next() {
        match a.as_str() {
            "--" => break,
            "-o" if build => {
                walk.next();
            }
            a => out.push(a),
        }
    }
    out
}

fn parse_args(args: &[String]) -> Result<Request, String> {
    let flags = flags(args);
    if args.first().is_some_and(|a| a == "help")
        || flags.iter().any(|a| *a == "-h" || *a == "--help")
    {
        return Ok(Request::Help);
    }
    if flags.iter().any(|a| *a == "-V" || *a == "--version") {
        return Ok(Request::Version);
    }
    let (command, rest) = args.split_first().ok_or("missing command")?;
    if !["fmt", "verify", "build", "asm"].contains(&command.as_str()) {
        return Err(format!("unknown command {command}"));
    }
    let mut a = Args {
        command: command.clone(),
        mode: FmtMode::Print,
        json: false,
        output: None,
        files: Vec::new(),
    };
    let mut options = true;
    let mut rest = rest.iter();
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "--" if options => options = false,
            "--json" if options => a.json = true,
            "-o" if options && command == "build" => {
                let out = rest.next().ok_or("-o needs the path of the executable")?;
                if a.output.replace(out.clone()).is_some() {
                    return Err("-o may be given once".into());
                }
            }
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
    if (command == "build" || command == "asm") && a.files.len() > 1 {
        return Err(format!("{command} takes one FILE"));
    }
    if command == "build" && a.output.is_none() {
        return Err("build needs -o OUTPUT, the executable to write".into());
    }
    if a.mode == FmtMode::Write && a.files.iter().any(|f| f == "-") {
        return Err("--write cannot rewrite standard input".into());
    }
    if a.files.iter().filter(|f| *f == "-").count() > 1 {
        return Err("- may be given once: standard input can be read only once".into());
    }
    Ok(Request::Run(a))
}

/// The bytes of `file`, or of standard input for `-`.
fn read(file: &str) -> Result<Vec<u8>, String> {
    if file == "-" {
        return streams::read_stdin().map_err(|e| format!("cannot read standard input: {e}"));
    }
    std::fs::read(file).map_err(|e| format!("cannot read {file}: {e}"))
}

/// The report on `file`, with no fields beyond the common ones yet.
pub(crate) fn file_report(file: &str, verdict: Verdict, problems: Vec<Problem>) -> Report {
    Report {
        file: file.to_string(),
        verdict,
        problems,
        extra: Vec::new(),
    }
}

/// Reads, parses and validates a file: its module, or the report that
/// rejects it.
pub(crate) fn load(file: &str, reg: &Registry) -> Result<Module, Report> {
    let bytes =
        read(file).map_err(|why| file_report(file, Verdict::IoError, vec![Problem::Io(why)]))?;
    let m = parse_bytes(&bytes, reg)
        .map_err(|e| file_report(file, Verdict::ParseError, vec![Problem::Parse(e)]))?;
    match verify(&m, reg) {
        ds if ds.is_empty() => Ok(m),
        ds => Err(file_report(
            file,
            Verdict::ValidationError,
            Problem::located(Kind::Validation, ds, &m.locs),
        )),
    }
}

fn verify_file(file: &str, reg: &Registry) -> Report {
    match load(file, reg) {
        Ok(_) => file_report(file, Verdict::Accepted, Vec::new()),
        Err(report) => report,
    }
}

/// A file that parsed: its module, and whether the file holds its
/// canonical text, when funk needs to know.
struct Formatted {
    module: Module,
    canonical: Option<bool>,
}

/// Formats one file. Returns the report and, if the file parsed, its
/// module. Only plain `fmt` without `--json` does not need to know whether
/// the file is canonical.
fn fmt_file(file: &str, mode: FmtMode, json: bool, reg: &Registry) -> (Report, Option<Formatted>) {
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
    let canonical = (mode != FmtMode::Print || json).then(|| is_canonical(&m, &bytes));
    let mut report = file_report(file, Verdict::Accepted, Vec::new());
    if let Some(c) = canonical {
        report.extra.push(("canonical", Json::Bool(c)));
    }
    if mode == FmtMode::Write
        && canonical == Some(false)
        && let Err(why) = replace(file, &m)
    {
        report.verdict = Verdict::IoError;
        report.problems.push(Problem::Io(why));
    }
    (
        report,
        Some(Formatted {
            module: m,
            canonical,
        }),
    )
}

/// Replaces the contents of `file` with the canonical text of `m` all at
/// once: streams the text into a new temporary file next to it, gives it the
/// file's permissions, then renames it over the file, so a failed write
/// leaves the file as it was. A file that funk may not write is left alone,
/// as is anything already at a temporary name.
fn replace(file: &str, m: &Module) -> Result<(), String> {
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
    let (tmp, out) = create_temp(&target).map_err(|e| cannot(&e))?;
    let written = write_temp(out, m, meta.permissions())
        .map_err(|e| format!("cannot write {}: {e}", tmp.display()))
        .and_then(|()| std::fs::rename(&tmp, &target).map_err(|e| cannot(&e)));
    if written.is_err() {
        let _ = std::fs::remove_file(&tmp);
    }
    written
}

/// Writes the canonical text of `m` to the temporary file `out`, gives it
/// `permissions` and syncs it.
fn write_temp(out: File, m: &Module, permissions: Permissions) -> io::Result<()> {
    let mut buffered = BufWriter::new(out);
    write!(buffered, "{}", Printed(m))?;
    let out = buffered
        .into_inner()
        .map_err(io::IntoInnerError::into_error)?;
    out.set_permissions(permissions)?;
    out.sync_all()
}

/// Writes `text` to `out` through a buffer, so that a text written in many
/// small pieces costs few writes.
fn stream(out: &mut impl Write, text: impl Display) -> io::Result<()> {
    let mut buffered = BufWriter::with_capacity(1 << 16, out);
    write!(buffered, "{text}")?;
    buffered.flush()
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
    let mut stderr = streams::stderr();
    match run_commands(args, &mut stderr) {
        Ok(status) => status,
        // A reader that stopped reading, as `head` does, wants no more
        // output and no message.
        Err(OutputError(_, e)) if e.kind() == std::io::ErrorKind::BrokenPipe => 2,
        Err(OutputError(what, e)) => {
            let _ = writeln!(stderr, "funk: cannot write {what}: {e}");
            2
        }
    }
}

fn run_commands(args: &[String], stderr: &mut impl Write) -> Result<u8, OutputError> {
    let mut stdout = streams::stdout();
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
        let mut assembly = None;
        let (report, formatted) = match (a.command.as_str(), &a.output) {
            ("verify", _) => (verify_file(file, &reg), None),
            ("asm", _) => {
                let (report, text) = build::asm_file(file, &reg);
                assembly = text;
                (report, None)
            }
            ("build", Some(out)) => (build::build_file(file, out, &reg), None),
            _ => fmt_file(file, a.mode, a.json, &reg),
        };
        let not_canonical = formatted
            .as_ref()
            .is_some_and(|f| f.canonical == Some(false));
        status = status.max(match report.verdict {
            Verdict::Accepted if a.mode == FmtMode::Check && not_canonical => 1,
            Verdict::Accepted => 0,
            Verdict::ParseError | Verdict::ValidationError | Verdict::Unsupported => 1,
            Verdict::IoError | Verdict::ToolError => 2,
        });
        if a.json {
            match &formatted {
                Some(f) if a.mode == FmtMode::Print => {
                    let head = report.json_open();
                    let text = JsonText(&f.module);
                    stream(&mut stdout, format_args!("{head},\"text\":\"{text}\"}}\n"))
                }
                _ => writeln!(stdout, "{}", report.json()),
            }
            .map_err(to_stdout)?;
        } else {
            for p in &report.problems {
                writeln!(stderr, "{}", p.text(file)).map_err(to_stderr)?;
            }
            match (a.mode, &formatted) {
                (FmtMode::Print, Some(f)) => stream(&mut stdout, Printed(&f.module)),
                (FmtMode::Check, Some(_)) if not_canonical => writeln!(stdout, "{file}"),
                _ => Ok(()),
            }
            .map_err(to_stdout)?;
            if let Some(text) = &assembly {
                stdout.write_all(text.as_bytes()).map_err(to_stdout)?;
            }
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
                    streams::stderr(),
                    "funk: argument {bad:?} is not UTF-8\n\n{USAGE}"
                );
                return ExitCode::from(2);
            }
        }
    }
    // A panic is an internal error: exit 2, as for any error that is not a
    // verdict on a file.
    let status = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(&args)));
    ExitCode::from(status.unwrap_or(2))
}
