//! `memcpy`, `memmove` and `memset` run as calls of funk's own routines,
//! which the module's object file carries, so a program that uses them
//! stays static, and one that also links the host's C library links with
//! no clash
//! (`docs/decisions/x86-64-backend-lowering-memory.md#copies-moves-and-sets`).

use std::path::{Path, PathBuf};
use std::process::Command;

use funk_ir::{Module, Registry, parse};
use funk_x86_64::{build, build_program, compile};

const COPIES: &str = "func @move(%v: i64, %k: i64, %n: i64) -> i64 {
^entry:
  %p: ptr = alloca stack i8 16 @0
  store nonatomic %v, %p @0
  %zero: i64 = const 0 @0
  %eight: i64 = const 8 @0
  %h: ptr = ptradd %p, %eight @0
  store nonatomic %zero, %h @0
  %q: ptr = ptradd %p, %k @0
  memmove nonatomic %q, %p, %n @0
  %w: i64 = load nonatomic %q @0
  ret %w @0
}

func @back(%v: i64, %n: i64) -> i64 {
^entry:
  %p: ptr = alloca stack i8 16 @0
  %one: i64 = const 1 @0
  %q: ptr = ptradd %p, %one @0
  store nonatomic %v, %q @0
  memmove nonatomic %p, %q, %n @0
  %w: i64 = load nonatomic %p @0
  ret %w @0
}

func @copy(%v: i64, %n: i16) -> i64 {
^entry:
  %p: ptr = alloca stack i64 2 @0
  store nonatomic %v, %p @0
  %eight: i64 = const 8 @0
  %q: ptr = ptradd %p, %eight @0
  %zero: i64 = const 0 @0
  store nonatomic %zero, %q @0
  memcpy nonatomic %q, %p, %n @0
  memcpy nonatomic %p, %p, %n @0
  %w: i64 = load nonatomic %q @0
  ret %w @0
}

func @set(%v: i8, %n: i128) -> i64 {
^entry:
  %p: ptr = alloca stack i64 @0
  %x: i64 = const -1 @0
  store nonatomic %x, %p @0
  memset nonatomic %p, %v, %n @0
  %w: i64 = load nonatomic %p @0
  ret %w @0
}

locs {
  @0 = unknown
}
";

/// A function that the module's object file links in from the host's C
/// library: `memcpy` and `memset`, which share names with funk's ops. The
/// module's text already ends with the note on the stack.
const CALLS_LIBC: &str = "\t.text
\t.globl\tfunk_test_libc
\t.type\tfunk_test_libc, @function
funk_test_libc:
\tcall\tmemcpy
\tcall\tmemset
\tret
";

/// The dynamic loader's path, which only an executable that it loads holds.
const LOADER: &str = "ld-linux-x86-64.so.2";

fn module() -> Module {
    parse(COPIES, &Registry::core()).unwrap()
}

/// A path for an executable named `name` in a fresh, empty directory.
fn fresh(name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("memops-{name}"));
    if dir.exists() {
        std::fs::remove_dir_all(&dir).unwrap();
    }
    std::fs::create_dir_all(&dir).unwrap();
    dir.join(name)
}

fn holds(exe: &Path, s: &str) -> bool {
    let bytes = std::fs::read(exe).unwrap();
    bytes.windows(s.len()).any(|w| w == s.as_bytes())
}

/// The value that `exe` prints for `func` on `args`.
fn run(exe: &Path, func: &str, args: &[&str]) -> String {
    let out = Command::new(exe).arg(func).args(args).output().unwrap();
    assert!(out.status.success(), "{func} {args:?}: {out:?}");
    let text = String::from_utf8(out.stdout).unwrap();
    let value = text
        .strip_prefix("{\"values\":[\"")
        .and_then(|t| t.strip_suffix("\"]}\n"))
        .unwrap_or_else(|| panic!("{text}"));
    value.to_string()
}

/// Every run of the module's functions, and what each gives: moves whose
/// ranges overlap, forwards and backwards, take what the source held
/// before they began; a copy onto its own range leaves it; a set writes
/// its byte; and a length of 0 does nothing.
fn check_runs(exe: &Path) {
    let v = "578437695752307201"; // 0x0807060504030201
    for (func, args, want) in [
        ("@move", vec![v, "1", "8"], v),
        ("@move", vec![v, "3", "8"], v),
        ("@move", vec![v, "1", "0"], "2259522249032450"),
        ("@move", vec![v, "0", "8"], v),
        ("@back", vec![v, "8"], v),
        ("@back", vec![v, "1"], "506097522914230529"),
        ("@copy", vec![v, "8"], v),
        ("@copy", vec![v, "3"], "197121"),
        ("@copy", vec![v, "0"], "0"),
        ("@set", vec!["1", "8"], "72340172838076673"),
        ("@set", vec!["0", "3"], "-16777216"),
        ("@set", vec!["7", "0"], "-1"),
    ] {
        assert_eq!(run(exe, func, &args), want, "{func} {args:?}");
    }
}

#[test]
fn a_program_that_copies_moves_and_sets_stays_static_and_runs() {
    let exe = fresh("static");
    build(&module(), &exe).unwrap();
    assert!(!holds(&exe, LOADER));
    check_runs(&exe);
}

/// The global symbols that the object file `object` defines, as GNU `nm`
/// lists them.
fn globals(object: &Path) -> Vec<String> {
    let out = Command::new("nm")
        .args(["-g", "--defined-only", "--format=just-symbols"])
        .arg(object)
        .output()
        .unwrap();
    assert!(out.status.success(), "{out:?}");
    let text = String::from_utf8(out.stdout).unwrap();
    text.lines().map(str::to_string).collect()
}

/// A global `memcpy` of the module would interpose on glibc's with no link
/// error, so the object file is checked for one: it defines only the
/// module's functions and the hand-written one, and the routines stay
/// local.
#[test]
fn funk_s_routines_link_beside_the_c_library_s() {
    let mut program = compile(&module()).unwrap();
    program.module.push_str(CALLS_LIBC);
    let exe = fresh("libc");
    let outputs = build_program(&program, &exe).unwrap();
    assert!(holds(&exe, LOADER));
    let mut defined = globals(&outputs.object);
    defined.sort();
    assert_eq!(defined, ["back", "copy", "funk_test_libc", "move", "set"]);
    check_runs(&exe);
}
