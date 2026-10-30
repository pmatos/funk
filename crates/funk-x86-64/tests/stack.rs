//! Frames larger than a page are probed, and a built executable runs each
//! function on a stack it reserves for it, so the process's stack limit does
//! not bound a frame (ADR-2026-10-30-1230, ADR-2026-10-30-1233).

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use funk_ir::{Attr, Block, Func, Location, Module, Op, dialects::core};
use funk_x86_64::build;

/// `@deep(%x: i64) -> i64`, which adds 1 to `%x` `n` times, one value per
/// add, so its frame holds about `n` slots of 8 bytes.
fn deep(m: &mut Module, n: usize) -> Func {
    let here = m.locs.push(Location::Unknown);
    let i64 = core::int_type(64);
    let one = Op::new("const", here)
        .attr(Attr::int(1))
        .result("one", i64.clone());
    let mut b = Block::new("entry").op(one);
    let mut last = "x".to_string();
    for k in 0..n {
        let v = format!("v{k}");
        let add = Op::new("add", here)
            .operand(last)
            .operand("one")
            .result(v.clone(), i64.clone());
        b = b.op(add);
        last = v;
    }
    b = b.op(Op::new("ret", here).operand(last));
    Func::new("deep")
        .param("x", i64.clone())
        .result(i64)
        .block(b)
}

/// `@seven() -> i8`, with a frame of one slot.
fn seven(m: &mut Module) -> Func {
    let here = m.locs.push(Location::Unknown);
    let i8 = core::int_type(8);
    Func::new("seven").result(i8.clone()).block(
        Block::new("entry")
            .op(Op::new("const", here).attr(Attr::int(7)).result("c", i8))
            .op(Op::new("ret", here).operand("c")),
    )
}

/// Builds `m` into a fresh directory named after `name`.
fn built(name: &str, m: &Module) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("stack-{name}"));
    if dir.exists() {
        std::fs::remove_dir_all(&dir).unwrap();
    }
    std::fs::create_dir_all(&dir).unwrap();
    let exe = dir.join(name);
    build(m, &exe).unwrap();
    exe
}

/// Runs `exe` with `args` after `sh` sets the limit `limit`, such as
/// `-s 8192`.
fn run_limited(limit: &str, exe: &Path, args: &[&str]) -> Output {
    Command::new("sh")
        .arg("-c")
        .arg(format!("ulimit {limit} && exec \"$0\" \"$@\""))
        .arg(exe)
        .args(args)
        .output()
        .unwrap()
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8(bytes.to_vec()).unwrap()
}

fn printed(out: &Output, value: &str) {
    assert_eq!(
        (out.status.code(), text(&out.stdout), text(&out.stderr)),
        (
            Some(0),
            format!("{{\"values\":[\"{value}\"]}}\n"),
            String::new()
        )
    );
}

#[test]
fn a_frame_well_over_8_mib_runs_under_an_8_mib_stack_limit() {
    let n = 10 << 17;
    let mut m = Module::new();
    let f = deep(&mut m, n);
    let exe = built("deep", &m.func(f));
    let want = (n + 5).to_string();
    printed(
        &Command::new(&exe).args(["@deep", "5"]).output().unwrap(),
        &want,
    );
    printed(&run_limited("-s 8192", &exe, &["@deep", "5"]), &want);
}

#[test]
fn a_stack_that_cannot_be_reserved_is_reported_in_one_line() {
    let n = 200_000;
    let mut m = Module::new();
    let (d, s) = (deep(&mut m, n), seven(&mut m));
    let exe = built("reserve", &m.func(d).func(s));
    printed(&run_limited("-d 1024", &exe, &["@seven"]), "7");
    let out = run_limited("-d 1024", &exe, &["@deep", "5"]);
    let err = text(&out.stderr);
    assert_eq!(out.status.code(), Some(2), "{err}");
    assert_eq!(text(&out.stdout), "");
    assert!(
        err.starts_with(&format!("{}: cannot reserve ", exe.display()))
            && err.ends_with(" bytes of stack for @deep\n")
            && err.lines().count() == 1,
        "{err}"
    );
    printed(
        &Command::new(&exe).args(["@deep", "5"]).output().unwrap(),
        &(n + 5).to_string(),
    );
}

#[test]
fn many_parameters_probe_the_wrapper_and_the_function() {
    let n = 600;
    let mut m = Module::new();
    let here = m.locs.push(Location::Unknown);
    let i64 = core::int_type(64);
    let mut f = Func::new("many").result(i64.clone());
    for j in 0..n {
        f = f.param(format!("a{j}"), i64.clone());
    }
    let add = |s: &str, a: &str, b: &str| {
        Op::new("add", here)
            .operand(a)
            .operand(b)
            .result(s, i64.clone())
    };
    let f = f.block(
        Block::new("entry")
            .op(add("s", "a0", "a6"))
            .op(add("t", "s", &format!("a{}", n - 1)))
            .op(Op::new("ret", here).operand("t")),
    );
    let exe = built("many", &m.func(f));
    let args: Vec<String> = (0..n).map(|j| (j * 1000).to_string()).collect();
    let mut argv = vec!["@many".to_string()];
    argv.extend(args);
    let out = run_limited(
        "-s 8192",
        &exe,
        &argv.iter().map(String::as_str).collect::<Vec<_>>(),
    );
    printed(&out, &((6 + n - 1) * 1000).to_string());
}
