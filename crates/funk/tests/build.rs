//! `funk build`: its outputs, its reports and its exit status
//! (ADR-2026-10-30-1233).

mod common;

use std::path::Path;
use std::process::Command;

use common::{DEAD, SEVEN, dir, expect, funk, funk_in, text, try_build};

/// A function with a parameter of `i7`, a value of `i33` and one of `i128`.
const ODD: &str = "func @odd(%a: i7) -> i7 {\n^entry:\n  %c: i33 = const 1 @1\n  %w: i128 = const 2 @2\n  ret %a @3\n}\n\nlocs {\n  @1 = \"w.c\":1:1 to 1:5\n  @2 = name(\"wide\")\n  @3 = unknown\n}\n";

/// A function with two results.
const PAIR: &str = "func @pair(%x: i8) -> i8, i8 {\n^entry:\n  ret %x, %x @4\n}\n\nlocs {\n  @4 = \"p.c\":2:3 to 2:12\n}\n";

/// Whether neither the executable nor the object file exists.
fn nothing_written(exe: &str) -> bool {
    !Path::new(exe).exists() && !Path::new(&format!("{exe}.o")).exists()
}

#[test]
fn build_writes_an_object_file_and_an_executable() {
    let (out, exe, src) = try_build("seven", SEVEN, &["--json"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    assert_eq!(
        text(&out.stdout),
        format!(
            "{{\"file\":\"{src}\",\"verdict\":\"accepted\",\"diagnostics\":[],\"object\":\"{exe}.o\",\"executable\":\"{exe}\"}}\n"
        )
    );
    let object = std::fs::read(format!("{exe}.o")).unwrap();
    let executable = std::fs::read(&exe).unwrap();
    // ELF, 64-bit, little-endian; a relocatable object and an executable.
    assert_eq!(&object[..6], b"\x7fELF\x02\x01");
    assert_eq!(object[16..18], [1, 0]);
    assert_eq!(executable[16..18], [2, 0]);
    let has = |bytes: &[u8], s: &str| bytes.windows(s.len()).any(|w| w == s.as_bytes());
    assert!(has(&object, "seven\0"));
    assert!(!has(&object, "__funk_start"));
    expect(Path::new(&exe), &["@seven"], &["7"]);
}

#[test]
fn build_is_silent_on_success_and_reads_standard_input() {
    let dir = dir("build-stdin");
    let exe = dir.join("seven").to_string_lossy().into_owned();
    let out = funk(&["build", "-o", &exe, "-"], SEVEN);
    assert_eq!(
        (out.status.code(), text(&out.stdout), text(&out.stderr)),
        (Some(0), String::new(), String::new())
    );
    expect(Path::new(&exe), &["@seven"], &["7"]);
}

#[test]
fn unsupported_widths_are_reported_at_their_ir_locations() {
    let (out, exe, src) = try_build("odd", ODD, &["--json"]);
    assert_eq!(out.status.code(), Some(1));
    let json = text(&out.stdout);
    assert!(
        json.starts_with(&format!(
            "{{\"file\":\"{src}\",\"verdict\":\"unsupported\",\"diagnostics\":["
        )),
        "{json}"
    );
    let lowers = "the x86-64 backend lowers i1, i8, i16, i32 and i64";
    for want in [
        format!(
            "{{\"kind\":\"unsupported\",\"message\":\"parameter %a: {lowers}, not i7\",\"func\":\"odd\",\"block\":\"entry\",\"op\":null,\"loc\":{{\"ref\":1,\"location\":\"\\\"w.c\\\":1:1 to 1:5\"}}}}"
        ),
        format!(
            "{{\"kind\":\"unsupported\",\"message\":\"%c: {lowers}, not i33\",\"func\":\"odd\",\"block\":\"entry\",\"op\":0,\"loc\":{{\"ref\":1,\"location\":\"\\\"w.c\\\":1:1 to 1:5\"}}}}"
        ),
        "\"message\":\"%w: the x86-64 backend does not lower i128 yet: it lowers i1, i8, i16, i32 and i64\",\"func\":\"odd\",\"block\":\"entry\",\"op\":1,\"loc\":{\"ref\":2,\"location\":\"name(\\\"wide\\\")\"}}".to_string(),
    ] {
        assert!(json.contains(&want), "{want}\nnot in\n{json}");
    }
    assert_eq!(json.matches("\"kind\"").count(), 3, "{json}");
    assert!(nothing_written(&exe));
    let (out, _, src) = try_build("odd-text", ODD, &[]);
    assert_eq!(out.status.code(), Some(1));
    assert!(text(&out.stderr).starts_with(&format!(
        "{src}: unsupported in @odd ^entry: parameter %a: {lowers}, not i7 (at @1 = \"w.c\":1:1 to 1:5)\n"
    )));
}

#[test]
fn more_than_one_result_is_reported_at_the_ret() {
    let (out, exe, src) = try_build("pair", PAIR, &[]);
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(
        text(&out.stderr),
        format!(
            "{src}: unsupported in @pair ^entry op 0: ret returns 2 values: the x86-64 backend returns at most one value so far (at @4 = \"p.c\":2:3 to 2:12)\n"
        )
    );
    assert!(nothing_written(&exe));
    let (out, _, _) = try_build("pair-json", PAIR, &["--json"]);
    let json = text(&out.stdout);
    assert!(
        json.contains("\"func\":\"pair\",\"block\":\"entry\",\"op\":0,\"loc\":{\"ref\":4,"),
        "{json}"
    );
}

#[test]
fn build_rejects_what_verify_rejects() {
    let (out, exe, _) = try_build("dead", DEAD, &["--json"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(text(&out.stdout).contains("\"verdict\":\"validation-error\""));
    assert!(nothing_written(&exe));
    let bad = SEVEN.replace("const 7", "const 7 7");
    let (out, exe, _) = try_build("parse", &bad, &["--json"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(text(&out.stdout).contains("\"verdict\":\"parse-error\""));
    assert!(nothing_written(&exe));
}

#[test]
fn build_needs_one_file_and_one_output() {
    for (args, why) in [
        (vec!["build", "f.fir"], "build needs -o OUTPUT"),
        (vec!["build", "f.fir", "-o"], "-o needs the path"),
        (
            vec!["build", "-o", "a", "-o", "b", "f.fir"],
            "-o may be given once",
        ),
        (
            vec!["build", "-o", "a", "f.fir", "g.fir"],
            "build takes one FILE",
        ),
        (vec!["build", "-o", "a"], "no FILE given"),
    ] {
        let out = funk(&args, "");
        assert_eq!(out.status.code(), Some(2), "{args:?}");
        assert!(
            text(&out.stderr).contains(why),
            "{args:?}: {}",
            text(&out.stderr)
        );
    }
}

#[test]
fn a_missing_assembler_is_a_tool_error() {
    let dir = dir("build-no-tools");
    let src = dir.join("seven.fir");
    std::fs::write(&src, SEVEN).unwrap();
    let exe = dir.join("seven").to_string_lossy().into_owned();
    let out = Command::new(env!("CARGO_BIN_EXE_funk"))
        .env("PATH", &dir)
        .args(["build", "--json", "-o", &exe, src.to_str().unwrap()])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(2));
    let json = text(&out.stdout);
    assert!(json.contains("\"verdict\":\"tool-error\""), "{json}");
    assert!(
        json.contains("cannot run the assembler, as: it is not installed"),
        "{json}"
    );
}

#[test]
fn an_output_that_starts_with_a_dash_is_a_path() {
    let dir = dir("build-dash");
    std::fs::write(dir.join("seven.fir"), SEVEN).unwrap();
    let out = funk_in(&dir, &["build", "-o", "-x", "seven.fir"], "");
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    expect(&dir.join("-x"), &["@seven"], &["7"]);
    assert!(dir.join("-x.o").exists());
}

#[test]
fn a_failed_link_leaves_no_object_file() {
    let dir = dir("build-link-fails");
    let src = dir.join("seven.fir");
    std::fs::write(&src, SEVEN).unwrap();
    let exe = dir.join("taken");
    std::fs::create_dir(&exe).unwrap();
    let exe = exe.to_string_lossy().into_owned();
    let out = funk(&["build", "--json", "-o", &exe, src.to_str().unwrap()], "");
    assert_eq!(out.status.code(), Some(2));
    assert!(text(&out.stdout).contains("\"verdict\":\"tool-error\""));
    assert!(!Path::new(&format!("{exe}.o")).exists());
}

#[test]
fn build_does_not_overwrite_its_input() {
    let dir = dir("build-onto-input");
    let src = dir.join("seven.fir");
    std::fs::write(&src, SEVEN).unwrap();
    let src = src.to_string_lossy().into_owned();
    let out = funk(&["build", "-o", &src, &src], "");
    assert_eq!(out.status.code(), Some(2));
    assert!(text(&out.stderr).contains("would overwrite the input"));
    assert_eq!(std::fs::read_to_string(&src).unwrap(), SEVEN);
    let exe = dir.join("seven").to_string_lossy().into_owned();
    let input = format!("{exe}.o");
    std::fs::write(&input, SEVEN).unwrap();
    let out = funk(&["build", "-o", &exe, &input], "");
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(std::fs::read_to_string(&input).unwrap(), SEVEN);
}
