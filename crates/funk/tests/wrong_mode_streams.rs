//! funk on a standard stream open in the wrong mode
//! (`docs/decisions/rust-ir-and-tools-funk.md#standard-streams`):
//! a standard input open only for writing, or a standard output or error
//! open only for reading. Every read or write on such a descriptor fails
//! with `EBADF`, and funk reports it as `fir-ref` does.

#![cfg(unix)]

mod common;

use std::process::{Command, Output};

use common::{SEVEN, check_unwritable_stderr, dir, file, text};

/// Runs funk with `args` from a shell that applies `redirect` first, with
/// `$STREAM` set to `path`, such as `1<"$STREAM"`, which opens standard
/// output on `path` for reading only.
fn funk_with(redirect: &str, path: &str, args: &[&str]) -> Output {
    Command::new("sh")
        .arg("-c")
        .arg(format!(r#"exec "$0" "$@" {redirect}"#))
        .arg(env!("CARGO_BIN_EXE_funk"))
        .args(args)
        .env("STREAM", path)
        .output()
        .unwrap()
}

#[test]
fn a_standard_input_open_only_for_writing_is_an_io_error() {
    let tmp = dir("write-only-stdin");
    let sink = tmp.join("sink");
    std::fs::write(&sink, "").unwrap();
    let sink = sink.to_str().unwrap();
    let out = tmp.join("seven");
    let out = out.to_str().unwrap();
    for args in [
        &["verify", "--json", "-"][..],
        &["fmt", "--json", "-"],
        &["fmt", "--check", "--json", "-"],
        &["build", "--json", "-o", out, "-"],
    ] {
        let run = funk_with(r#"0>>"$STREAM""#, sink, args);
        assert_eq!(run.status.code(), Some(2), "{args:?}");
        let json = text(&run.stdout);
        assert!(
            json.starts_with(concat!(
                r#"{"file":"-","verdict":"io-error","diagnostics":"#,
                r#"[{"kind":"io-error","message":"cannot read standard input: "#,
            )),
            "{args:?}: {json}"
        );
    }
    for args in [
        &["verify", "-"][..],
        &["fmt", "-"],
        &["fmt", "--check", "-"],
        &["build", "-o", out, "-"],
    ] {
        let run = funk_with(r#"0>>"$STREAM""#, sink, args);
        assert_eq!(run.status.code(), Some(2), "{args:?}");
        let err = text(&run.stderr);
        assert!(
            err.starts_with("-: error: cannot read standard input: "),
            "{args:?}: {err}"
        );
    }
    assert_eq!(std::fs::read(sink).unwrap(), b"");
}

#[test]
fn a_standard_output_open_only_for_reading_is_a_failed_write() {
    let seven = file("read-only-stdout.fir", SEVEN);
    let nc = file(
        "read-only-stdout-nc.fir",
        &SEVEN.replacen("  %c", "    %c", 1),
    );
    let out = dir("read-only-stdout").join("seven");
    let out = out.to_str().unwrap();
    for args in [
        &["--help"][..],
        &["help"],
        &["--version"],
        &["verify", "--json", &seven],
        &["fmt", &seven],
        &["fmt", "--check", &nc],
        &["fmt", "--json", &seven],
        &["build", "--json", "-o", out, &seven],
    ] {
        let run = funk_with(r#"1<"$STREAM""#, &seven, args);
        assert_eq!(run.status.code(), Some(2), "{args:?}");
        let err = text(&run.stderr);
        assert!(
            err.starts_with("funk: cannot write standard output: "),
            "{args:?}: {err}"
        );
        assert!(!err.contains("panicked"), "{err}");
    }
}

#[test]
fn a_run_that_writes_nothing_to_an_unwritable_standard_output_exits_as_before() {
    let seven = file("read-only-stdout-unused.fir", SEVEN);
    let out = dir("read-only-stdout-unused").join("seven");
    let out = out.to_str().unwrap();
    for args in [
        &["verify", &seven][..],
        &["fmt", "--check", &seven],
        &["build", "-o", out, &seven],
    ] {
        let run = funk_with(r#"1<"$STREAM""#, &seven, args);
        assert_eq!(run.status.code(), Some(0), "{args:?}");
        assert_eq!(text(&run.stderr), "", "{args:?}");
    }
}

#[test]
fn a_standard_error_open_only_for_reading_fails_each_diagnostic() {
    let seven = file("read-only-stderr.fir", SEVEN);
    check_unwritable_stderr("read-only-stderr", |args| {
        funk_with(r#"2<"$STREAM""#, &seven, args)
    });
}
