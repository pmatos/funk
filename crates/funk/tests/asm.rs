//! `funk asm`: the assembly of a module's functions, and its reports.

mod common;

use common::{SEVEN, file, funk, text};

const ODD: &str =
    "func @odd(%a: i7) -> i7 {\n^entry:\n  ret %a @1\n}\n\nlocs {\n  @1 = unknown\n}\n";

#[test]
fn asm_prints_the_assembly_of_the_functions_with_a_comment_for_each_op() {
    let out = funk(&["asm", "-"], SEVEN);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    let asm = text(&out.stdout);
    assert!(asm.contains("seven:"), "{asm}");
    assert!(asm.contains("# %c: i32 = const 7 @0"), "{asm}");
    assert!(
        !asm.contains("_start"),
        "the entry file is not shown: {asm}"
    );
}

#[test]
fn asm_json_holds_the_same_assembly_as_text() {
    let plain = text(&funk(&["asm", "-"], SEVEN).stdout);
    let out = funk(&["asm", "--json", "-"], SEVEN);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    let report = text(&out.stdout);
    assert!(report.contains("\"verdict\":\"accepted\""), "{report}");
    let escaped = plain
        .replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\t', "\\t");
    assert!(
        report.contains(&format!("\"text\":\"{escaped}\"")),
        "{report}"
    );
}

#[test]
fn asm_reports_what_the_backend_cannot_lower_with_its_location() {
    let out = funk(&["asm", "--json", "-"], ODD);
    assert_eq!(out.status.code(), Some(1));
    let report = text(&out.stdout);
    assert!(report.contains("\"verdict\":\"unsupported\""), "{report}");
    assert!(report.contains("\"loc\":{\"ref\":1"), "{report}");
    assert!(!report.contains("\"text\""), "{report}");
    let plain = funk(&["asm", "-"], ODD);
    assert_eq!(plain.status.code(), Some(1));
    assert!(plain.stdout.is_empty());
    assert!(text(&plain.stderr).contains("not i7"));
}

#[test]
fn asm_rejects_a_module_that_is_not_valid_and_takes_one_file() {
    let bad = "func @f() -> i32 {\n^entry:\n  ret @0\n}\n\nlocs {\n  @0 = unknown\n}\n";
    let out = funk(&["asm", "--json", "-"], bad);
    assert_eq!(out.status.code(), Some(1));
    assert!(text(&out.stdout).contains("\"verdict\":\"validation-error\""));
    let a = file("asm-a.fir", SEVEN);
    let out = funk(&["asm", &a, &a], "");
    assert_eq!(out.status.code(), Some(2));
    assert!(text(&out.stderr).contains("asm takes one FILE"));
}
