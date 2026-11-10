//! A program whose object file references a symbol it does not define links
//! with the host's C library, and one that does not stays static
//! (ADR-2026-11-10-1303). fir cannot declare a C function yet (#239), so the
//! program that calls one is the entry point of a compiled module with its
//! function's assembly written by hand.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use funk_ir::{Module, Registry, parse};
use funk_x86_64::{build, build_program, compile};

const GREET: &str =
    "func @greet(%x: i32) -> i32 {\n^entry:\n  ret %x @0\n}\n\nlocs {\n  @0 = unknown\n}\n";

/// `greet(x)`: prints `C got X` with `printf`, then returns `x + 1`.
const GREET_IN_C: &str = "\t.text
\t.globl\tgreet
\t.type\tgreet, @function
greet:
\tpushq\t%rbp
\tmovq\t%rsp, %rbp
\tsubq\t$16, %rsp
\tmovl\t%edi, -4(%rbp)
\tmovl\t%edi, %esi
\tleaq\t.Lformat(%rip), %rdi
\txorl\t%eax, %eax
\tcall\tprintf
\tmovl\t-4(%rbp), %eax
\tincl\t%eax
\tleave
\tret
\t.section\t.rodata
.Lformat:\t.asciz\t\"C got %d\\n\"
\t.section\t.note.GNU-stack,\"\",@progbits
";

/// The dynamic loader's path, which only an executable that it loads holds.
const LOADER: &str = "ld-linux-x86-64.so.2";

fn module(text: &str) -> Module {
    parse(text, &Registry::core()).unwrap()
}

/// A path for an executable named `name` in a fresh, empty directory.
fn fresh(name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("libc-{name}"));
    if dir.exists() {
        std::fs::remove_dir_all(&dir).unwrap();
    }
    std::fs::create_dir_all(&dir).unwrap();
    dir.join(name)
}

/// `greet` built with its body calling the C library's `printf`.
fn greet_in_c(name: &str) -> PathBuf {
    let mut program = compile(&module(GREET)).unwrap();
    program.module = GREET_IN_C.to_string();
    let exe = fresh(name);
    build_program(&program, &exe).unwrap();
    exe
}

fn holds(exe: &Path, s: &str) -> bool {
    let bytes = std::fs::read(exe).unwrap();
    bytes.windows(s.len()).any(|w| w == s.as_bytes())
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8(bytes.to_vec()).unwrap()
}

fn report(out: &Output) -> (Option<i32>, String, String) {
    (out.status.code(), text(&out.stdout), text(&out.stderr))
}

#[test]
fn a_function_that_calls_printf_runs_and_its_output_comes_first() {
    let exe = greet_in_c("greet");
    assert!(holds(&exe, LOADER));
    let out = Command::new(&exe).args(["@greet", "41"]).output().unwrap();
    assert_eq!(
        report(&out),
        (
            Some(0),
            "C got 41\n{\"values\":[\"42\"]}\n".to_string(),
            String::new()
        )
    );
}

#[test]
fn a_bad_command_line_still_exits_with_2() {
    let exe = greet_in_c("usage");
    let out = Command::new(&exe).args(["@greet"]).output().unwrap();
    assert_eq!(
        report(&out),
        (
            Some(2),
            String::new(),
            format!("{}: @greet takes 1 arguments, not 0\n", exe.display())
        )
    );
}

#[test]
fn output_that_the_c_library_cannot_write_exits_with_2() {
    let exe = greet_in_c("full");
    let full = std::fs::OpenOptions::new()
        .write(true)
        .open("/dev/full")
        .unwrap();
    let out = Command::new(&exe)
        .args(["@greet", "1"])
        .stdout(Stdio::from(full))
        .output()
        .unwrap();
    assert_eq!(report(&out), (Some(2), String::new(), String::new()));
}

#[test]
fn a_program_that_needs_nothing_else_stays_static() {
    let exe = fresh("static");
    let program = compile(&module(GREET)).unwrap();
    assert!(!program.entry.contains(".Lfunk_libc, 1"));
    build(&module(GREET), &exe).unwrap();
    assert!(!holds(&exe, LOADER));
    let out = Command::new(&exe).args(["@greet", "41"]).output().unwrap();
    assert_eq!(
        report(&out),
        (
            Some(0),
            "{\"values\":[\"41\"]}\n".to_string(),
            String::new()
        )
    );
}

#[test]
fn a_symbol_that_no_library_defines_is_a_link_error() {
    let mut program = compile(&module(GREET)).unwrap();
    program.module = GREET_IN_C.replace("printf", "funk_no_such_function");
    let err = build_program(&program, &fresh("missing")).unwrap_err();
    let funk_x86_64::BuildError::Tool(said) = err else {
        panic!("{err:?}")
    };
    assert!(said.contains("funk_no_such_function"), "{said}");
}
