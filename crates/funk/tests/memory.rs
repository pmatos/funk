//! Memory run natively (#231): `alloca`, `load`, `store` and `ptradd` in
//! the default memory, and in another memory of bytes
//! (`docs/decisions/x86-64-backend-lowering-memory.md`). A value stored and
//! loaded back is itself at every width, an `i1` reads back as a byte of 0
//! or 1, a narrower load reads the low bytes, each pass of a loop allocates
//! anew, and an allocation larger than its stack reports that it ran out.

#![cfg(unix)]

mod common;

use std::path::Path;
use std::process::{Command, Output};

use common::{boundaries, build, expect, module, spell, text};
use funk_x86_64::width::{ONE_REGISTER, PAIR};

/// `@round_W(%v: iW) -> iW`: stores `%v` in an allocation of its own and
/// loads it back.
fn round_trip(w: u32) -> String {
    format!(
        "func @round_{w}(%v: i{w}) -> i{w} {{
^entry:
  %p: ptr = alloca stack i{w} @0
  store nonatomic %v, %p @0
  %r: i{w} = load nonatomic %p @0
  ret %r @0
}}
"
    )
}

/// Functions on bytes, pointers and loops.
fn shapes() -> Vec<String> {
    let mut out: Vec<String> = ONE_REGISTER
        .into_iter()
        .chain([PAIR])
        .map(round_trip)
        .collect();
    out.push(
        "func @padding(%v: i1) -> i8 {
^entry:
  %p: ptr = alloca stack i8 @0
  store nonatomic %v, %p @0
  %r: i8 = load nonatomic %p @0
  ret %r @0
}
"
        .into(),
    );
    out.push(
        "func @narrower(%v: i32) -> i16, i8 {
^entry:
  %p: ptr = alloca stack i32 @0
  store nonatomic %v, %p @0
  %lo: i16 = load nonatomic %p @0
  %one: i1 = const true @0
  %two: i64 = const 2 @0
  %q: ptr = ptradd %p, %two @0
  %r: ptr = ptradd %q, %one @0
  %b: i8 = load nonatomic %r @0
  ret %lo, %b @0
}
"
        .into(),
    );
    out.push(
        "func @through(%v: i64) -> i64 {
^entry:
  %p: ptr = alloca stack i64 @0
  %s: ptr = alloca stack ptr align(64) @0
  store nonatomic %v, %p @0
  store nonatomic %p, %s @0
  %q: ptr = load nonatomic %s @0
  %r: i64 = load nonatomic %q @0
  ret %r @0
}
"
        .into(),
    );
    // Each pass stores its count in a new allocation and keeps the first
    // one, which still holds 0 after the last pass.
    out.push(
        "func @passes(%n: i32) -> i32, i32 {
^entry:
  %z: i32 = const 0 @0
  %p0: ptr = alloca stack i32 @0
  store nonatomic %z, %p0 @0
  br ^head(%z, %p0) @0
^head(%i: i32, %last: ptr):
  %done: i1 = icmp sge %i, %n @0
  cond_br %done, ^exit, ^body @0
^body:
  %one: i32 = const 1 @0
  %j: i32 = add %i, %one @0
  %q: ptr = alloca stack i32 @0
  store nonatomic %j, %q @0
  br ^head(%j, %q) @0
^exit:
  %first: i32 = load nonatomic %p0 @0
  %end: i32 = load nonatomic %last @0
  ret %first, %end @0
}
"
        .into(),
    );
    // `%k` KiB on each of `%n` passes.
    out.push(
        "func @grow(%n: i32) -> i32 {
^entry:
  %z: i32 = const 0 @0
  br ^head(%z) @0
^head(%i: i32):
  %done: i1 = icmp sge %i, %n @0
  cond_br %done, ^exit, ^body @0
^body:
  %p: ptr = alloca stack i8 65536 @0
  %one: i32 = const 1 @0
  %j: i32 = add %i, %one @0
  store nonatomic %j, %p @0
  br ^head(%j) @0
^exit:
  ret %i @0
}
"
        .into(),
    );
    out.push(
        "func @big() -> i8 {
^entry:
  %p: ptr = alloca stack i8 1048576 align(8388608) @0
  %c: i8 = const 7 @0
  %k: i64 = const 1048575 @0
  %q: ptr = ptradd %p, %k @0
  store nonatomic %c, %q @0
  %r: i8 = load nonatomic %q @0
  ret %r @0
}
"
        .into(),
    );
    out
}

#[test]
fn a_value_stored_and_loaded_back_is_itself_at_every_width() {
    let exe = build("memory-round", &module(&shapes()));
    for w in ONE_REGISTER {
        for v in boundaries(w) {
            let s = spell(w, v);
            expect(&exe, &[&format!("@round_{w}"), &s], &[&s]);
        }
    }
    for v in [0, 1, -1, i128::MIN, i128::MAX, 1 << 64] {
        let s = v.to_string();
        expect(&exe, &["@round_128", &s], &[&s]);
    }
    expect(&exe, &["@padding", "true"], &["1"]);
    expect(&exe, &["@padding", "false"], &["0"]);
    expect(&exe, &["@narrower", "67305985"], &["513", "2"]);
    expect(&exe, &["@through", "-5"], &["-5"]);
    expect(&exe, &["@big"], &["7"]);
}

#[test]
fn each_pass_of_a_loop_allocates_anew() {
    let exe = build("memory-passes", &module(&shapes()));
    expect(&exe, &["@passes", "0"], &["0", "0"]);
    expect(&exe, &["@passes", "5"], &["0", "5"]);
    expect(&exe, &["@grow", "16"], &["16"]);
}

/// Runs `exe` with `args` under a stack limit of 1 MiB and an address
/// space of 1 GiB, set for its own process by `sh`.
fn run_small(exe: &Path, args: &[&str]) -> Output {
    Command::new("sh")
        .arg("-c")
        .arg("ulimit -s 1024 && ulimit -v 1048576 && exec \"$0\" \"$@\"")
        .arg(exe)
        .args(args)
        .output()
        .unwrap()
}

/// A loop that allocates is unbounded, as a recursion is: it gets the
/// process's stack limit, and says so when it outgrows it.
#[test]
fn a_loop_that_outgrows_its_stack_says_so() {
    let exe = build("memory-grow", &module(&shapes()));
    let out = run_small(&exe, &["@grow", "8"]);
    assert_eq!(text(&out.stdout), "{\"values\":[\"8\"]}\n", "{out:?}");
    let out = run_small(&exe, &["@grow", "64"]);
    let program = exe.display().to_string();
    assert_eq!(out.status.code(), Some(2), "{out:?}");
    assert_eq!(text(&out.stdout), "");
    assert_eq!(
        text(&out.stderr),
        format!("{program}: @grow ran out of the 1048576 bytes of stack reserved for it\n")
    );
}

/// A memory other than 0 whose units are bytes and pointers 64 bits runs
/// as memory 0 does; one of other units is reported where its pointer is
/// defined.
#[test]
fn a_memory_of_bytes_runs_and_another_is_reported() {
    let bytes = format!(
        "layout memory(1, unit(8), pointer(64), little, align(16))\n\n{}",
        module(&["func @one(%v: i16) -> i16 {
^entry:
  %p: ptr(1) = alloca stack i16 @0
  %s: ptr = alloca stack ptr(1) @0
  store nonatomic %v, %p @0
  store nonatomic %p, %s @0
  %q: ptr(1) = load nonatomic %s @0
  %r: i16 = load nonatomic %q @0
  ret %r @0
}
"
        .into()])
    );
    let exe = build("memory-one", &bytes);
    expect(&exe, &["@one", "-300"], &["-300"]);
    let wide = bytes.replace("unit(8)", "unit(16)");
    let (out, _, _) = common::try_build("memory-wide", &wide, &[]);
    assert_eq!(out.status.code(), Some(1), "{out:?}");
    let report = text(&out.stdout) + &text(&out.stderr);
    assert!(
        report.contains("memory 1 of 16-bit units and 64-bit little pointers"),
        "{report}"
    );
}
