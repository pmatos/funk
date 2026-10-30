//! `funk fmt` and `funk verify` on files, as text and as JSON.

mod common;

use std::process::Command;

use common::{DEAD, SEVEN, dir, file, funk, funk_in, text};

const BAD_TYPES: &str = "func @f(%a: i32, %b: i64) -> i32 {\n^entry:\n  %c: i32 = add %a, %b @0\n  ret %c @0\n}\n\nlocs {\n  @0 = unknown\n}\n";

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
    assert_eq!(funk(&["verify", "-", "-"], "").status.code(), Some(2));
    for help in [
        &["--help"][..],
        &["help"],
        &["fmt", "--help"],
        &["verify", "x.fir", "-h"],
    ] {
        let out = funk(help, "");
        assert_eq!(out.status.code(), Some(0), "{help:?}");
        assert!(text(&out.stdout).starts_with("usage: funk"), "{help:?}");
    }
    assert!(text(&funk(&["--version"], "").stdout).starts_with("funk "));
}

#[cfg(unix)]
#[test]
fn an_argument_that_is_not_utf8_is_a_usage_error() {
    use std::os::unix::ffi::OsStrExt;
    let out = Command::new(env!("CARGO_BIN_EXE_funk"))
        .arg("verify")
        .arg(std::ffi::OsStr::from_bytes(b"bad\xff.fir"))
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(2));
    assert!(text(&out.stderr).contains("is not UTF-8"));
}

#[test]
fn text_mode_prints_each_validation_error_on_its_own_line() {
    let path = file(
        "two-errors.fir",
        &DEAD
            .replace("const 1 @1", "const 1 @9")
            .replace("ret %d @1", "ret %d @9"),
    );
    let out = funk(&["verify", &path], "");
    assert_eq!(out.status.code(), Some(1));
    let err = text(&out.stderr);
    let lines: Vec<&str> = err.lines().collect();
    assert_eq!(lines.len(), 3, "{err}");
    let prefix = format!("{path}: validation error in @f ^dead");
    assert!(lines.iter().all(|l| l.starts_with(&prefix)), "{err}");
    assert!(lines[1].ends_with("op 0: location reference @9 is not in the location table (at @9)"));
}

#[test]
fn quoted_symbols_are_spelled_canonically_in_every_report() {
    let hidden = "func @\"\\u{85}\\u{202e}\"() {\n^e:\n  ret @0\n}\n";
    let path = file(
        "hidden.fir",
        &format!("{hidden}\n{hidden}\nlocs {{\n  @0 = unknown\n}}\n"),
    );
    let out = funk(&["verify", &path], "");
    assert_eq!(
        text(&out.stderr),
        format!(
            "{path}: validation error in @\"\\u{{85}}\\u{{202e}}\": the symbol @\"\\u{{85}}\\u{{202e}}\" names more than one item\n"
        )
    );
    let out = funk(&["verify", "--json", &path], "");
    let json = text(&out.stdout);
    assert!(json.contains(r#""func":"\u0085\u202e""#), "{json}");
    assert!(
        !json.trim_end().chars().any(funk_ir::text::is_escaped),
        "{json:?}"
    );
    let path = file(
        "inject.fir",
        "func @\"a\\nb\\u{1b}[31mRED\\u{202e}x\"() {\n^e:\n  ret %x @0\n}\n\nlocs {\n  @0 = unknown\n}\n",
    );
    let out = funk(&["verify", &path], "");
    let err = text(&out.stderr);
    assert_eq!(err.lines().count(), 1, "{err:?}");
    assert!(
        err.ends_with("in @\"a\\nb\\u{1b}[31mRED\\u{202e}x\"\n"),
        "{err:?}"
    );
    assert!(
        !err.trim_end().chars().any(funk_ir::text::is_escaped),
        "{err:?}"
    );
}

#[test]
fn the_exit_status_is_the_largest_over_the_files() {
    let seven = file("status-seven.fir", SEVEN);
    let bad = file("status-bad.fir", BAD_TYPES);
    let missing = "/nonexistent/status.fir";
    for (files, status) in [
        (&[seven.as_str(), bad.as_str()][..], 1),
        (&[bad.as_str(), seven.as_str()], 1),
        (&[missing, bad.as_str()], 2),
        (&[bad.as_str(), missing, seven.as_str()], 2),
    ] {
        for cmd in ["fmt", "verify"] {
            let mut args = vec![cmd];
            args.extend(files);
            assert_eq!(funk(&args, "").status.code(), Some(status), "{args:?}");
        }
    }
}

#[test]
fn fmt_check_json_reports_canonical_and_sets_the_exit_status() {
    let messy = file("check-json.fir", &SEVEN.replace("  ret", "\tret"));
    let clean = file("check-json-clean.fir", SEVEN);
    let out = funk(&["fmt", "--check", "--json", &messy, &clean], "");
    assert_eq!(out.status.code(), Some(1));
    let lines: Vec<String> = text(&out.stdout).lines().map(String::from).collect();
    assert_eq!(
        lines,
        [
            format!(
                r#"{{"file":"{messy}","verdict":"accepted","diagnostics":[],"canonical":false}}"#
            ),
            format!(
                r#"{{"file":"{clean}","verdict":"accepted","diagnostics":[],"canonical":true}}"#
            ),
        ]
    );
    let out = funk(&["fmt", "--check", "--json", &clean], "");
    assert_eq!(out.status.code(), Some(0));
}

#[test]
fn files_after_double_dash_are_files_even_when_they_look_like_options() {
    let cwd = dir("dash");
    std::fs::write(cwd.join("--odd.fir"), SEVEN).unwrap();
    std::fs::write(cwd.join("-h"), SEVEN).unwrap();
    let out = funk_in(&cwd, &["verify", "--json", "--", "--odd.fir", "-h"], "");
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    let json = text(&out.stdout);
    assert!(
        json.starts_with(r#"{"file":"--odd.fir","verdict":"accepted""#),
        "{json}"
    );
    assert!(
        json.contains(r#"{"file":"-h","verdict":"accepted""#),
        "{json}"
    );
    let out = funk_in(&cwd, &["verify", "--odd.fir"], "");
    assert_eq!(out.status.code(), Some(2));
    assert!(text(&out.stderr).starts_with("funk: unknown option --odd.fir"));
}

#[cfg(target_os = "linux")]
#[test]
fn output_that_cannot_be_written_is_an_io_error() {
    let full = || std::fs::File::create("/dev/full").unwrap();
    let seven = file("full.fir", SEVEN);
    for args in [&["--help"][..], &["--version"], &["fmt", &seven]] {
        let out = Command::new(env!("CARGO_BIN_EXE_funk"))
            .args(args)
            .stdout(full())
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(2), "{args:?}");
        let err = text(&out.stderr);
        assert!(
            err.starts_with("funk: cannot write standard output: "),
            "{err}"
        );
        assert!(!err.contains("panicked"), "{err}");
    }
}
