//! funk on a standard input, output or error that was closed when it
//! started (ADR-2026-11-02-2253, ADR-2026-11-03-0107): the targets where
//! `funk-start-fds` records them.

#![cfg(any(
    target_os = "linux",
    target_os = "android",
    target_os = "freebsd",
    target_os = "dragonfly",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "illumos",
    target_os = "solaris"
))]

mod common;

use std::process::{Command, Output, Stdio};

use common::{DEAD, SEVEN, check_unwritable_stderr, dir, file, text};

/// Runs funk with `args` from a shell that applies `redirect` first, such as
/// `<&-`, which closes standard input.
fn funk_with(redirect: &str, args: &[&str]) -> Output {
    Command::new("sh")
        .arg("-c")
        .arg(format!(r#"exec "$0" "$@" {redirect}"#))
        .arg(env!("CARGO_BIN_EXE_funk"))
        .args(args)
        .output()
        .unwrap()
}

#[test]
fn a_closed_standard_input_is_an_io_error() {
    let out = dir("closed-stdin").join("seven");
    let out = out.to_str().unwrap();
    for args in [
        &["verify", "--json", "-"][..],
        &["fmt", "--json", "-"],
        &["build", "--json", "-o", out, "-"],
    ] {
        let run = funk_with("<&-", args);
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
    for args in [&["verify", "-"][..], &["fmt", "-"]] {
        let run = funk_with("<&-", args);
        assert_eq!(run.status.code(), Some(2), "{args:?}");
        let err = text(&run.stderr);
        assert!(
            err.starts_with("-: error: cannot read standard input: "),
            "{args:?}: {err}"
        );
    }
}

#[test]
fn a_closed_standard_output_is_a_failed_write() {
    let seven = file("closed-stdout.fir", SEVEN);
    let nc = file("closed-stdout-nc.fir", &SEVEN.replacen("  %c", "    %c", 1));
    let out = dir("closed-stdout").join("seven");
    let out = out.to_str().unwrap();
    for args in [
        &["--help"][..],
        &["--version"],
        &["verify", "--json", &seven],
        &["fmt", &seven],
        &["fmt", "--check", &nc],
        &["fmt", "--json", &seven],
        &["build", "--json", "-o", out, &seven],
    ] {
        let run = funk_with(">&-", args);
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
fn a_closed_standard_error_fails_each_diagnostic() {
    check_unwritable_stderr("closed-stderr", |args| funk_with("2>&-", args));
}

#[test]
fn a_closed_descriptor_that_funk_does_not_use_is_no_error() {
    let seven = file("closed-unused.fir", SEVEN);
    let run = funk_with(">&-", &["verify", &seven]);
    assert_eq!(run.status.code(), Some(0), "{}", text(&run.stderr));
    assert_eq!(text(&run.stderr), "");
    let run = funk_with("<&-", &["verify", "--json", &seven]);
    assert_eq!(run.status.code(), Some(0), "{}", text(&run.stderr));
    assert!(text(&run.stdout).contains(r#""verdict":"accepted""#));
}

/// `<>` opens `/dev/null` for reading and writing, as Python's
/// `subprocess.DEVNULL` and the standard library's own reopening do.
#[test]
fn open_descriptors_on_dev_null_behave_as_before() {
    let seven = file("dev-null.fir", SEVEN);
    let nc = file("dev-null-nc.fir", &SEVEN.replacen("  %c", "    %c", 1));
    let bad = file("dev-null-bad.fir", "func @f(\n");
    let dead = file("dev-null-dead.fir", DEAD);
    let out = dir("dev-null").join("seven");
    let out = out.to_str().unwrap();
    let direct = || Command::new(env!("CARGO_BIN_EXE_funk"));
    for args in [
        &["verify", "--json", "-"][..],
        &["fmt", "--json", "-"],
        &["build", "--json", "-o", out, "-"],
    ] {
        let run = direct().args(args).stdin(Stdio::null()).output().unwrap();
        assert_eq!(run.status.code(), Some(1), "{args:?}");
        let parse_error = r#"{"file":"-","verdict":"parse-error""#;
        assert!(text(&run.stdout).starts_with(parse_error), "{args:?}");
        for redirect in ["</dev/null", "<>/dev/null"] {
            let run = funk_with(redirect, args);
            assert_eq!(run.status.code(), Some(1), "{redirect} {args:?}");
            assert!(
                text(&run.stdout).starts_with(parse_error),
                "{redirect} {args:?}"
            );
        }
    }
    for (args, status) in [
        (&["--version"][..], 0),
        (&["verify", "--json", &seven], 0),
        (&["fmt", &seven], 0),
        (&["fmt", "--json", &seven], 0),
        (&["fmt", "--check", &nc], 1),
        (&["build", "--json", "-o", out, &seven], 0),
    ] {
        let run = direct().args(args).stdout(Stdio::null()).output().unwrap();
        assert_eq!(run.status.code(), Some(status), "{args:?}");
        assert_eq!(text(&run.stderr), "", "{args:?}");
        for redirect in [">/dev/null", "1<>/dev/null"] {
            let run = funk_with(redirect, args);
            assert_eq!(run.status.code(), Some(status), "{redirect} {args:?}");
            assert_eq!(text(&run.stderr), "", "{redirect} {args:?}");
        }
    }
    for args in [
        &["fmt", &bad][..],
        &["verify", &bad],
        &["verify", &dead],
        &["build", "-o", out, &dead],
    ] {
        let run = direct().args(args).stderr(Stdio::null()).output().unwrap();
        assert_eq!(run.status.code(), Some(1), "{args:?}");
        for redirect in ["2>/dev/null", "2<>/dev/null"] {
            let run = funk_with(redirect, args);
            assert_eq!(run.status.code(), Some(1), "{redirect} {args:?}");
        }
    }
}
