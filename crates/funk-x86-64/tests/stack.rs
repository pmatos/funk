//! Frames of a page or more are probed, and a built executable runs each
//! function on a stack it reserves for it, so the process's stack limit does
//! not bound a frame (ADR-2026-10-30-1230, ADR-2026-10-30-1233). That stack
//! covers every call the function can make (ADR-2026-11-02-1132).

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use funk_ir::{Attr, Block, Func, Location, Module, Op, dialects::core};
use funk_x86_64::build;
use funk_x86_64::frame::size_for;

/// `@deep(%x: i64) -> i64`, which adds 1 to `%x` `n` times, one value per
/// add, so its frame holds about `n` slots of 8 bytes.
fn deep(m: &mut Module, n: usize) -> Func {
    chained(m, "deep", n, &[])
}

/// `@name(%x: i64) -> i64`, which adds 1 to `%x` `n` times, one value per
/// add, then passes the sum through a call to each of `callees` in turn,
/// and returns what the last one gives: `n + 2` values, and one more for
/// each call.
fn chained(m: &mut Module, name: &str, n: usize, callees: &[&str]) -> Func {
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
    for (k, callee) in callees.iter().enumerate() {
        let r = format!("r{k}");
        let call = Op::new("call", here)
            .attr(Attr::Sym(callee.to_string()))
            .operand(last)
            .result(r.clone(), i64.clone());
        b = b.op(call);
        last = r;
    }
    b = b.op(Op::new("ret", here).operand(last));
    Func::new(name).param("x", i64.clone()).result(i64).block(b)
}

/// The stack that the table gives a function of one parameter, a run of
/// which needs `need` bytes below its return address: the wrapper's return
/// address, saved `%rbp` and frame of one slot, and 16 KiB for the
/// runtime, rounded up to a page.
fn figure(need: usize) -> usize {
    (need + 16 + 16 + 16 * 1024).div_ceil(4096) * 4096
}

/// The bytes of a function's frame of `values` values, and its return
/// address and saved `%rbp`.
fn own(values: usize) -> usize {
    usize::try_from(size_for(values).unwrap()).unwrap() + 16
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

/// Checks that `out` reports, in one line, that the stack of `bytes` bytes
/// for `@name` cannot be reserved.
fn cannot_reserve(out: &Output, exe: &Path, bytes: usize, name: &str) {
    assert_eq!(
        (out.status.code(), text(&out.stdout), text(&out.stderr)),
        (
            Some(2),
            String::new(),
            format!(
                "{}: cannot reserve {bytes} bytes of stack for @{name}\n",
                exe.display()
            )
        )
    );
}

/// `@top` calls `@mid`, which calls `@leaf`, each with a frame of more
/// than a megabyte: far more than the 16 KiB of slack that a stack sized
/// from `@top`'s frame alone had. The figure is the sum of the three, as
/// the report of a stack that a limit of 1 MiB cannot hold shows.
#[test]
fn the_stack_of_a_run_covers_each_frame_of_a_chain_of_calls() {
    let n = 150_000;
    let mut m = Module::new();
    let top = chained(&mut m, "top", n, &["mid"]);
    let mid = chained(&mut m, "mid", n, &["leaf"]);
    let leaf = chained(&mut m, "leaf", n, &[]);
    let exe = built("chain", &m.func(top).func(mid).func(leaf));
    printed(
        &Command::new(&exe).args(["@top", "5"]).output().unwrap(),
        &(3 * n + 5).to_string(),
    );
    printed(
        &run_limited("-s 8192", &exe, &["@top", "5"]),
        &(3 * n + 5).to_string(),
    );
    let leaf = own(n + 2);
    let mid = own(n + 3) + leaf;
    let top = own(n + 3) + mid;
    for (name, need) in [("top", top), ("mid", mid), ("leaf", leaf)] {
        let out = run_limited("-d 1024", &exe, &[&format!("@{name}"), "5"]);
        cannot_reserve(&out, &exe, figure(need), name);
    }
}

/// `@spiral` calls `@deep`, with its frame of more than a megabyte, and
/// then itself without end. It is recursive, so it asks for as much stack
/// as memory allows, but it needs at least a run's stack with no call in
/// a cycle: its own frame and `@deep`'s. A limit of 1 MiB cannot hold that,
/// and the report names those bytes.
#[test]
fn a_recursive_run_needs_at_least_the_stack_of_its_calls_out_of_the_cycle() {
    let n = 150_000;
    let mut m = Module::new();
    let spiral = chained(&mut m, "spiral", 0, &["deep", "spiral"]);
    let d = deep(&mut m, n);
    let exe = built("spiral", &m.func(spiral).func(d));
    let need = own(4) + own(n + 2);
    let out = run_limited("-d 1024", &exe, &["@spiral", "5"]);
    cannot_reserve(&out, &exe, figure(need), "spiral");
}
