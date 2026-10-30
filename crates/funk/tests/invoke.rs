//! How a built executable is invoked: the function by its fir name, its
//! arguments spelled as fir constants, and a bad command line reported in
//! one line on standard error with exit status 2 (ADR-2026-10-30-1233).

mod common;

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use common::{build, expect, func, module, run, text};

fn program(name: &str) -> PathBuf {
    build(
        name,
        &module(&[
            func("i1", "%x: i1", "i1", &["ret %x"]),
            func("i8", "%x: i8", "i8", &["ret %x"]),
            func("i64", "%x: i64", "i64", &["ret %x"]),
            func("two", "%a: i8, %b: i8", "i8", &["ret %b"]),
        ]),
    )
}

/// Runs `exe` with `args` and checks that it fails with status 2, prints
/// nothing on standard output, and says `why` on standard error.
fn refused(exe: &Path, args: &[&str], why: &str) {
    let out = run(exe, args);
    let err = text(&out.stderr);
    assert_eq!(out.status.code(), Some(2), "{args:?}: {err}");
    assert_eq!(text(&out.stdout), "", "{args:?}");
    assert!(err.contains(why), "{args:?}: {err}");
    assert!(
        err.ends_with('\n') && err.lines().count() == 1,
        "{args:?}: {err}"
    );
}

#[test]
fn a_function_is_named_as_fir_writes_it() {
    let exe = program("names");
    expect(&exe, &["@two", "1", "2"], &["2"]);
    let shown = exe.display().to_string();
    let out = run(&exe, &[]);
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(
        text(&out.stderr),
        format!("usage: {shown} @FUNCTION ARG...\n")
    );
    refused(&exe, &["two", "1", "2"], "no function two in this program");
    refused(
        &exe,
        &["@\"two\"", "1", "2"],
        "no function @\"two\" in this program",
    );
    refused(&exe, &["@tw"], "no function @tw in this program");
    refused(&exe, &["@twos"], "no function @twos in this program");
    refused(&exe, &["@two", "1"], "@two takes 2 arguments, not 1");
    refused(
        &exe,
        &["@two", "1", "2", "3"],
        "@two takes 2 arguments, not 3",
    );
}

#[test]
fn arguments_take_the_spelling_of_fir_constants() {
    let exe = program("spellings");
    expect(&exe, &["@i1", "true"], &["true"]);
    expect(&exe, &["@i1", "false"], &["false"]);
    for v in ["0", "1", "-1", "-128", "127", "99", "-10"] {
        expect(&exe, &["@i8", v], &[v]);
    }
    for v in [
        "9223372036854775807",
        "-9223372036854775808",
        "1000000000000",
    ] {
        expect(&exe, &["@i64", v], &[v]);
    }
    let bad = [
        (
            "@i1",
            vec![
                "1", "0", "-1", "True", "TRUE", "", "true ", "truex", "f", "yes",
            ],
        ),
        (
            "@i8",
            vec![
                "128", "-129", "-0", "007", "00", "+1", "", "-", "1x", " 1", "1 ", "0x10", "1e2",
                "true", "--1",
            ],
        ),
        (
            "@i64",
            vec![
                "9223372036854775808",
                "-9223372036854775809",
                "18446744073709551616",
                "-18446744073709551616",
                "99999999999999999999999",
            ],
        ),
    ];
    for (f, args) in bad {
        let ty = &f[1..];
        for arg in args {
            refused(
                &exe,
                &[f, arg],
                &format!("{arg} is not a value of type {ty}"),
            );
        }
    }
}

#[test]
fn control_characters_from_the_command_line_are_escaped() {
    let exe = program("controls");
    refused(&exe, &["@i8", "1\n2"], "1\\x0a2 is not a value of type i8");
    refused(
        &exe,
        &["@no\r\u{7f}\tne"],
        "no function @no\\x0d\\x7f\\x09ne in this program",
    );
    refused(
        &exe,
        &["@two", "1", "\u{1b}[31m"],
        "\\x1b[31m is not a value of type i8",
    );
    refused(&exe, &["@i8", "é"], "é is not a value of type i8");
    use std::os::unix::process::CommandExt;
    let out = Command::new(&exe).arg0("a\nb").output().unwrap();
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(text(&out.stderr), "usage: a\\x0ab @FUNCTION ARG...\n");
}

#[test]
fn a_closed_pipe_ends_the_program_with_status_2() {
    let exe = program("pipe");
    let (reader, writer) = std::io::pipe().unwrap();
    drop(reader);
    let out = Command::new(&exe)
        .args(["@i8", "5"])
        .stdout(Stdio::from(writer))
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(2), "{out:?}");
    assert_eq!(text(&out.stderr), "");
}
