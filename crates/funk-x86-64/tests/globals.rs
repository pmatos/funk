//! Globals and `globaladdr` as native code (#237 stage 3,
//! `docs/decisions/x86-64-backend-lowering-memory.md#globals`): each
//! global of the module's own table goes to `.rodata`, `.data` or `.bss`
//! with its alignment, an `addr` piece is a `.quad` relocation, and
//! `globaladdr` is a `leaq` relative to `%rip`.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;

use funk_ir::{Module, Registry, parse};
use funk_x86_64::{build, compile};

const GLOBALS: &str = "global @msg() size(8) align(1) const units(104, 105, 0) {
}

global @table() size(32) align(8) addr(@msg) addr(@msg, 1) addr(@counter) {
}

global @counter() size(4) align(4) {
}

global @page() size(16) align(4096) export units(1) zeros(3) units(2) {
}

func @msg_unit(%i: i64) -> i8 {
^entry:
  %m: ptr = globaladdr @msg @0
  %p: ptr = ptradd %m, %i @0
  %v: i8 = load nonatomic %p @0
  ret %v @0
}

func @follow(%i: i64) -> i8 {
^entry:
  %t: ptr = globaladdr @table @0
  %k: i64 = const 8 @0
  %o: i64 = mul %i, %k @0
  %e: ptr = ptradd %t, %o @0
  %p: ptr = load nonatomic %e @0
  %v: i8 = load nonatomic %p @0
  ret %v @0
}

func @bump(%x: i32) -> i32 {
^entry:
  %t: ptr = globaladdr @table @0
  %k: i64 = const 16 @0
  %e: ptr = ptradd %t, %k @0
  %c: ptr = load nonatomic %e @0
  %v: i32 = load nonatomic %c @0
  %s: i32 = add %v, %x @0
  store nonatomic %s, %c @0
  %d: ptr = globaladdr @counter @0
  %r: i32 = load nonatomic %d @0
  ret %r @0
}

func @page_unit(%i: i64) -> i8 {
^entry:
  %g: ptr = globaladdr @page @0
  %p: ptr = ptradd %g, %i @0
  %v: i8 = load nonatomic %p @0
  ret %v @0
}

func @page_misalignment() -> i64 {
^entry:
  %g: ptr = globaladdr @page @0
  %a: i64 = ptr_expose %g @0
  %k: i64 = const 4096 @0
  %r: i64 = urem %a, %k @0
  ret %r @0
}

func @write_msg(%x: i8) {
^entry:
  %m: ptr = globaladdr @msg @0
  store nonatomic %x, %m @0
  ret @0
}

locs {
  @0 = unknown
}
";

fn module(text: &str) -> Module {
    parse(text, &Registry::core()).unwrap()
}

/// `items` followed by the location table.
fn with_locs(items: &str) -> String {
    format!("{items}\n\nlocs {{\n  @0 = unknown\n}}\n")
}

/// A path for an executable named `name` in a fresh, empty directory.
fn fresh(name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("globals-{name}"));
    if dir.exists() {
        std::fs::remove_dir_all(&dir).unwrap();
    }
    std::fs::create_dir_all(&dir).unwrap();
    dir.join(name)
}

/// The value that `exe` prints for `func` on `args`.
fn run(exe: &Path, func: &str, args: &[&str]) -> String {
    let out = Command::new(exe).arg(func).args(args).output().unwrap();
    assert!(out.status.success(), "{func} {args:?}: {out:?}");
    let text = String::from_utf8(out.stdout).unwrap();
    text.strip_prefix("{\"values\":[\"")
        .and_then(|t| t.strip_suffix("\"]}\n"))
        .unwrap_or_else(|| panic!("{text}"))
        .to_string()
}

/// Each symbol that the object file `object` defines, with the letter of
/// its kind as GNU `nm` lists it: `r`, `d` or `b` for read-only data, data
/// or `.bss`, upper case when the symbol is global.
fn symbols(object: &Path) -> Vec<(String, char)> {
    let out = Command::new("nm")
        .args(["--defined-only", "--format=posix"])
        .arg(object)
        .output()
        .unwrap();
    assert!(out.status.success(), "{out:?}");
    let text = String::from_utf8(out.stdout).unwrap();
    text.lines()
        .filter_map(|l| {
            let mut w = l.split_whitespace();
            Some((w.next()?.to_string(), w.next()?.chars().next()?))
        })
        .collect()
}

#[test]
fn globals_hold_their_initializers_and_their_addresses_reach_them() {
    let exe = fresh("runs");
    let outputs = build(&module(GLOBALS), &exe).unwrap();
    for (func, args, want) in [
        ("@msg_unit", vec!["0"], "104"),
        ("@msg_unit", vec!["1"], "105"),
        ("@msg_unit", vec!["2"], "0"),
        ("@msg_unit", vec!["7"], "0"),
        ("@follow", vec!["0"], "104"),
        ("@follow", vec!["1"], "105"),
        ("@follow", vec!["2"], "0"),
        ("@bump", vec!["5"], "5"),
        ("@page_unit", vec!["0"], "1"),
        ("@page_unit", vec!["3"], "0"),
        ("@page_unit", vec!["4"], "2"),
        ("@page_unit", vec!["15"], "0"),
        ("@page_misalignment", vec![], "0"),
    ] {
        assert_eq!(run(&exe, func, &args), want, "{func} {args:?}");
    }
    let mut syms = symbols(&outputs.object);
    syms.retain(|(s, _)| ["msg", "table", "counter", "page"].contains(&s.as_str()));
    syms.sort();
    let want = [
        ("counter", 'b'),
        ("msg", 'r'),
        ("page", 'D'),
        ("table", 'd'),
    ];
    let want: Vec<(String, char)> = want.iter().map(|(s, c)| (s.to_string(), *c)).collect();
    assert_eq!(syms, want);
}

#[test]
fn a_store_to_a_constant_global_faults() {
    let exe = fresh("rodata");
    build(&module(GLOBALS), &exe).unwrap();
    let out = Command::new(&exe)
        .args(["@write_msg", "1"])
        .output()
        .unwrap();
    assert_eq!(out.status.signal(), Some(11), "{out:?}");
    assert!(out.stdout.is_empty(), "{out:?}");
}

#[test]
fn a_module_without_globals_has_no_data() {
    let text = with_locs("func @f() -> i8 {\n^entry:\n  %c: i8 = const 1 @0\n  ret %c @0\n}");
    let asm = compile(&module(&text)).unwrap().module;
    for s in [".data", ".bss", ".rodata", ".quad"] {
        assert!(!asm.contains(s), "{s}\n{asm}");
    }
}

#[test]
fn an_address_piece_is_a_relocation_with_its_offset_wrapped() {
    let text = with_locs(
        "global @a() size(1) align(1) units(9) {\n}\n\n\
         global @b() size(16) align(8) const addr(@a, 18446744073709551615) addr(@b, 8) {\n}",
    );
    let asm = compile(&module(&text)).unwrap().module;
    assert!(asm.contains("\t.quad\ta+18446744073709551615\n"), "{asm}");
    assert!(asm.contains("\t.quad\tb+8\n"), "{asm}");
    let exe = fresh("wrapped");
    build(&module(&text), &exe).unwrap();
}

#[test]
fn a_global_the_backend_cannot_place_is_reported_at_the_global() {
    for (items, global, why) in [
        (
            "layout memory(1, unit(16), pointer(32), little)\n\n\
             global @w() memory(1) size(2) align(2) units(1) {\n}",
            "w",
            "memory 1 of 16-bit units",
        ),
        (
            "layout memory(1, unit(8), pointer(32), little)\n\n\
             global @n() memory(1) size(4) align(4) {\n}\n\n\
             global @p() size(4) align(4) addr(@n) {\n}",
            "p",
            "a pointer of memory 1",
        ),
        (
            "global @big() size(1073741825) align(1) {\n}",
            "big",
            "at most 2^30 bytes",
        ),
        (
            "global @a() size(1073741824) align(1) {\n}\n\n\
             global @b() size(1) align(1) {\n}",
            "b",
            "at most 2^30 bytes",
        ),
    ] {
        let Err(ds) = compile(&module(&with_locs(items))) else {
            panic!("{items} compiled");
        };
        assert!(
            ds.iter()
                .any(|d| d.func.as_deref() == Some(global) && d.message.contains(why)),
            "{items}: {ds:?}"
        );
    }
}

/// `as` warns on `.zero 0`, and a build fails on any warning, so a global
/// of size 0 and a `zeros(0)` piece write no `.zero`.
#[test]
fn empty_globals_and_pieces_build() {
    let text = with_locs(
        "global @none() size(0) align(1) {\n}\n\n\
         global @some() size(2) align(1) units(1) zeros(0) units(2) {\n}\n\n\
         global @tail() size(1) align(1) const zeros(0) {\n}\n\n\
         func @f() -> i8 {\n^entry:\n  %g: ptr = globaladdr @some @0\n  \
         %v: i8 = load nonatomic %g @0\n  ret %v @0\n}",
    );
    let asm = compile(&module(&text)).unwrap().module;
    assert!(!asm.contains(".zero\t0"), "{asm}");
    let exe = fresh("empty");
    build(&module(&text), &exe).unwrap();
    assert_eq!(run(&exe, "@f", &[]), "1");
}

#[test]
fn a_nested_module_s_globals_are_left_out() {
    let text = with_locs(
        "module @dev() {\n  global @cell() size(4) align(4) units(1) {\n  }\n\n}\n\n\
         func @f() -> i8 {\n^entry:\n  %c: i8 = const 1 @0\n  ret %c @0\n}",
    );
    let asm = compile(&module(&text)).unwrap().module;
    assert!(!asm.contains("cell"), "{asm}");
}
