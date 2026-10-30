//! `funk fmt` and `funk verify` on files, as text and as JSON.

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

const SEVEN: &str = "func @seven() -> i32 {\n^entry:\n  %c: i32 = const 7 @0\n  ret %c @0\n}\n\nlocs {\n  @0 = unknown\n}\n";
const DEAD: &str = "func @f() -> i32 {\n^entry:\n  %c: i32 = const 0 @0\n  ret %c @0\n^dead:\n  %d: i32 = const 1 @1\n  ret %d @1\n}\n\nlocs {\n  @0 = unknown\n  @1 = \"f.c\":3:1 to 3:9\n}\n";
const BAD_TYPES: &str = "func @f(%a: i32, %b: i64) -> i32 {\n^entry:\n  %c: i32 = add %a, %b @0\n  ret %c @0\n}\n\nlocs {\n  @0 = unknown\n}\n";

/// Writes `text` to a fresh file named `name` and returns its path.
fn file(name: &str, text: &str) -> String {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("cli");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, text).unwrap();
    path.to_string_lossy().into_owned()
}

fn funk(args: &[&str], stdin: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_funk"))
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(stdin.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8(bytes.to_vec()).unwrap()
}

#[test]
fn fmt_prints_the_canonical_form() {
    let messy = SEVEN
        .replace("  ret %c @0", "\tret   %c @0 // done")
        .trim_end()
        .to_string();
    let path = file("messy.fir", &messy);
    let out = funk(&["fmt", &path], "");
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    assert_eq!(text(&out.stdout), SEVEN);
    let out = funk(&["fmt", "-"], &messy);
    assert_eq!(text(&out.stdout), SEVEN);
}

#[test]
fn fmt_check_and_write_act_on_files_that_are_not_canonical() {
    let messy = file(
        "check.fir",
        &SEVEN.replace("locs {\n  @0 = unknown\n}", "locs { @0 = unknown }"),
    );
    let clean = file("clean.fir", SEVEN);
    let out = funk(&["fmt", "--check", &messy, &clean], "");
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(text(&out.stdout), format!("{messy}\n"));
    let out = funk(&["fmt", "--write", &messy, &clean], "");
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    assert_eq!(std::fs::read_to_string(&messy).unwrap(), SEVEN);
    assert_eq!(funk(&["fmt", "--check", &messy], "").status.code(), Some(0));
}

#[test]
fn fmt_does_not_validate() {
    let path = file("fmt-dead.fir", DEAD);
    let out = funk(&["fmt", &path], "");
    assert_eq!(out.status.code(), Some(0));
    assert_eq!(text(&out.stdout), DEAD);
}

#[test]
fn verify_is_silent_on_a_valid_module() {
    let out = funk(&["verify", &file("seven.fir", SEVEN)], "");
    assert_eq!(
        (out.status.code(), out.stdout.len(), out.stderr.len()),
        (Some(0), 0, 0)
    );
}

#[test]
fn a_parse_error_carries_its_text_position() {
    let path = file("bad-types.fir", BAD_TYPES);
    for cmd in ["fmt", "verify"] {
        let out = funk(&[cmd, &path], "");
        assert_eq!(out.status.code(), Some(1));
        let err = text(&out.stderr);
        assert!(
            err.starts_with(&format!("{path}:3:13: parse error: op add does not decode")),
            "{err}"
        );
        let out = funk(&[cmd, "--json", &path], "");
        let json = text(&out.stdout);
        assert!(json.contains(r#""verdict":"parse-error""#), "{json}");
        assert!(
            json.contains(r#""kind":"parse-error""#) && json.contains(r#""line":3,"column":13"#),
            "{json}"
        );
    }
}

#[test]
fn a_validation_error_carries_its_ir_location() {
    let path = file("dead.fir", DEAD);
    let out = funk(&["verify", &path], "");
    assert_eq!(out.status.code(), Some(1));
    let err = text(&out.stderr);
    assert_eq!(
        err,
        format!(
            "{path}: validation error in @f ^dead: block ^dead is not reachable from the entry (at @1 = \"f.c\":3:1 to 3:9)\n"
        )
    );
    let out = funk(&["verify", "--json", &path], "");
    let json = text(&out.stdout);
    let expected = r#""verdict":"validation-error","diagnostics":[{"kind":"validation-error","message":"block ^dead is not reachable from the entry","func":"f","block":"dead","op":null,"loc":{"ref":1,"location":"\"f.c\":3:1 to 3:9"}}]}"#;
    assert!(json.ends_with(&format!("{expected}\n")), "{json}");
}

#[test]
fn json_reports_one_line_per_file() {
    let ok = file("json-ok.fir", SEVEN);
    let out = funk(
        &["verify", "--json", &ok, &file("json-dead.fir", DEAD), "-"],
        "locs {\n}\n",
    );
    let lines: Vec<String> = text(&out.stdout).lines().map(String::from).collect();
    assert_eq!(lines.len(), 3);
    assert_eq!(
        lines[0],
        format!(r#"{{"file":"{ok}","verdict":"accepted","diagnostics":[]}}"#)
    );
    assert!(lines[1].contains("validation-error"));
    assert_eq!(
        lines[2],
        r#"{"file":"-","verdict":"accepted","diagnostics":[]}"#
    );
    let out = funk(&["fmt", "--json", "-"], "locs { }");
    assert_eq!(
        text(&out.stdout),
        "{\"file\":\"-\",\"verdict\":\"accepted\",\"diagnostics\":[],\"canonical\":false,\"text\":\"locs {\\n}\\n\"}\n"
    );
}

#[test]
fn usage_and_io_errors_exit_with_2() {
    for args in [
        &[][..],
        &["build"],
        &["fmt"],
        &["verify", "--check", "x"],
        &["fmt", "--write", "-"],
        &["fmt", "--check", "--write", "x"],
    ] {
        let out = funk(args, "");
        assert_eq!(out.status.code(), Some(2), "{args:?}");
        assert!(text(&out.stderr).contains("usage: funk"), "{args:?}");
    }
    let out = funk(&["verify", "--json", "/nonexistent/x.fir"], "");
    assert_eq!(out.status.code(), Some(2));
    assert!(text(&out.stdout).contains(r#""verdict":"io-error""#));
    assert_eq!(funk(&["--help"], "").status.code(), Some(0));
    assert!(text(&funk(&["--version"], "").stdout).starts_with("funk "));
}
