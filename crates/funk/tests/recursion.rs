//! The stack of a recursive run (ADR-2026-11-02-1132): it follows the
//! process's stack limit, `ulimit -s`, as a C or Rust program's does, so
//! recursion goes as deep as that limit allows, and a run that outgrows its
//! stack says so in one line, with exit status 2.
//!
//! A run whose outcome depends on `ulimit -s` sets it for its own process,
//! through `sh`, since the limit that the tests inherit differs from machine
//! to machine; the tests' own process keeps its limit. Raising it, to
//! 64 MiB or to `unlimited`, needs a hard limit at least that high, as
//! Linux gives by default. Every run of a recursive function is made under
//! `ulimit -v`, a limit on the address space a process maps, and some also
//! under `ulimit -d`, a limit on its data. Under `ulimit -s unlimited` alone
//! a recursive run's stack would be as large as the machine's memory and
//! swap, and a run that recursed without end, which a regression could
//! make of any run here, would use them all before it reached the end.

#![cfg(unix)]

mod common;

use std::io::Read;
use std::os::unix::process::ExitStatusExt;
use std::path::Path;
use std::process::{Child, Command, Output, Stdio};
use std::time::{Duration, Instant};

use common::{build, dir, module, text, values};

/// The limit on data, in KiB, under which runs that never end are made with
/// no stack limit: 64 MiB.
const LIMIT: u64 = 64 * 1024;

/// `@forever` calls itself without end; `@ping` and `@pong` call each
/// other without end; `@outer` calls `@forever`, and `@"for ever"` calls
/// itself. `@count` counts `%n` down to zero, one call at a time, and
/// `@even` and `@odd` call each other `%n` times.
fn recursive() -> String {
    let forever = |name: &str, callee: &str| {
        format!(
            "func {name}(%n: i64) -> i64 {{
^entry:
  %one: i64 = const 1 @0
  %m: i64 = add %n, %one @0
  %r: i64 = call {callee} %m @0
  ret %r @0
}}
"
        )
    };
    let parity = |name: &str, other: &str, at_zero: &str| {
        format!(
            "func @{name}(%n: i64) -> i1 {{
^entry:
  %zero: i64 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const {at_zero} @0
  ret %r @0
^more:
  %one: i64 = const 1 @0
  %m: i64 = sub %n, %one @0
  %o: i1 = call @{other} %m @0
  ret %o @0
}}
"
        )
    };
    let count = "func @count(%n: i64) -> i64 {
^entry:
  %zero: i64 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  ret %zero @0
^more:
  %one: i64 = const 1 @0
  %m: i64 = sub %n, %one @0
  %c: i64 = call @count %m @0
  %s: i64 = add %c, %one @0
  ret %s @0
}
";
    let outer = "func @outer(%n: i64) -> i64 {
^entry:
  %r: i64 = call @forever %n @0
  ret %r @0
}
";
    module(&[
        forever("@forever", "@forever"),
        forever("@ping", "@pong"),
        forever("@pong", "@ping"),
        outer.into(),
        forever("@\"for ever\"", "@\"for ever\""),
        count.into(),
        parity("even", "odd", "true"),
        parity("odd", "even", "false"),
    ])
}

/// Runs `exe` with `args` after `sh` sets each of `limits`, such as
/// `-s 8192`, for the run's process only.
fn run_under(limits: &[&str], exe: &Path, args: &[&str]) -> Output {
    let set: String = limits.iter().map(|l| format!("ulimit {l} && ")).collect();
    Command::new("sh")
        .arg("-c")
        .arg(format!("{set}exec \"$0\" \"$@\""))
        .arg(exe)
        .args(args)
        .output()
        .unwrap()
}

/// Runs `exe` with `args` after `sh` limits the data it maps to `kib` KiB,
/// and its address space to 16 MiB more.
fn run_limited(kib: u64, exe: &Path, args: &[&str]) -> Output {
    let (data, space) = (format!("-d {kib}"), format!("-v {}", kib + 16 * 1024));
    run_under(&[&data, &space], exe, args)
}

/// A limit on the address space, 1 GiB, set with each stack limit below,
/// so that no run here can fill the machine: under it, a runtime that
/// ignored `ulimit -s` would fail a test that recurses without end
/// instead, and under `ulimit -s unlimited` the runtime halves memory and
/// swap until the stack fits, which still leaves far more than 8 MiB.
const GUARD: &str = "-v 1048576";

/// The stack limit that Linux gives a process by default, 8 MiB, and its
/// bytes.
const DEFAULT: [&str; 2] = ["-s 8192", GUARD];
const DEFAULT_BYTES: u64 = 8192 * 1024;

/// A small stack limit, 1 MiB, and its bytes.
const SMALL: [&str; 2] = ["-s 1024", GUARD];
const SMALL_BYTES: u64 = 1024 * 1024;

/// A stack limit that is not a whole number of pages, 1023 KiB, and its
/// bytes rounded down to a page, which the runtime reserves.
const ODD: [&str; 2] = ["-s 1023", GUARD];
const ODD_BYTES: u64 = 1023 * 1024 / 4096 * 4096;

/// A large stack limit: 64 MiB.
const LARGE: [&str; 2] = ["-s 65536", GUARD];

/// No stack limit (`RLIM_INFINITY`): a recursive run's stack is then as
/// large as memory and swap, or under the guard as large as fits in it.
const UNLIMITED: [&str; 2] = ["-s unlimited", GUARD];

/// Checks that `out` is the report of a run of `name` by the program
/// `program` that outgrew its stack, and returns the bytes it names: one
/// line on standard error, nothing on standard output, exit status 2.
fn ran_out(out: &Output, program: &str, name: &str) -> u64 {
    let err = text(&out.stderr);
    assert_eq!(
        (out.status.code(), text(&out.stdout)),
        (Some(2), "".into()),
        "{err}"
    );
    let bytes = err
        .strip_prefix(&format!("{program}: {name} ran out of the "))
        .and_then(|s| s.strip_suffix(" bytes of stack reserved for it\n"))
        .and_then(|n| n.parse::<u64>().ok());
    bytes.unwrap_or_else(|| panic!("not the report of {name} outgrowing its stack: {err:?}"))
}

/// Checks that `out` is a run that returned `value`.
fn returned(out: &Output, value: &str) {
    assert_eq!(
        (out.status.code(), text(&out.stdout), text(&out.stderr)),
        (Some(0), values(&[value]), String::new())
    );
}

/// Under the default stack limit, a run that recurses without end gets
/// 8 MiB of stack, as a C or Rust program does, and reports at once that
/// it ran out of exactly that.
#[test]
fn a_run_that_recurses_without_end_reports_that_it_ran_out_of_stack() {
    let exe = build("recursion-forever", &recursive());
    let program = exe.display().to_string();
    for name in ["@forever", "@ping", "@pong", "@outer", "@\"for ever\""] {
        let start = Instant::now();
        let out = run_under(&DEFAULT, &exe, &[name, "0"]);
        assert!(start.elapsed() < Duration::from_secs(10), "{name}");
        assert_eq!(ran_out(&out, &program, name), DEFAULT_BYTES, "{name}");
    }
}

/// With no stack limit, a recursive run asks for memory and swap, and the
/// runtime halves that until the kernel grants it, so under a data limit
/// each run's stack is more than a quarter of the limit, and less than all.
#[test]
fn with_no_stack_limit_a_data_limit_bounds_a_recursive_run() {
    let exe = build("recursion-unlimited", &recursive());
    let program = exe.display().to_string();
    let (data, space) = (format!("-d {LIMIT}"), format!("-v {}", LIMIT + 16 * 1024));
    let limits = [UNLIMITED[0], &data, &space];
    let limit = LIMIT * 1024;
    for name in ["@forever", "@ping", "@pong", "@outer", "@\"for ever\""] {
        let bytes = ran_out(&run_under(&limits, &exe, &[name, "0"]), &program, name);
        assert!(
            bytes.is_multiple_of(4096) && bytes > limit / 4 && bytes < limit,
            "{bytes}"
        );
    }
    returned(&run_under(&limits, &exe, &["@count", "200000"]), "200000");
    let small = [UNLIMITED[0], "-d 1024", "-v 17408"];
    returned(&run_under(&small, &exe, &["@count", "1000"]), "1000");
}

/// The program's path, which the report starts with, shows each control
/// byte as `\xHH`, as every other report does (ADR-2026-10-30-1233).
#[test]
fn the_report_shows_control_bytes_in_the_program_s_path_escaped() {
    let exe = build("recursion-path", &recursive());
    let odd = exe.with_file_name("ever\nmore");
    std::fs::copy(&exe, &odd).unwrap();
    let shown = odd.display().to_string().replace('\n', "\\x0a");
    ran_out(
        &run_limited(LIMIT, &odd, &["@forever", "0"]),
        &shown,
        "@forever",
    );
}

/// A launcher that blocks SIGSEGV and then runs its arguments as a command.
/// It is a static executable of its own because Rust's `Command` unblocks
/// every signal in the child; a blocked signal stays blocked across execve.
const BLOCKING: &str = "\t.globl\t_start
_start:
\tmovl\t$14, %eax\t\t# rt_sigprocmask
\txorl\t%edi, %edi\t\t# SIG_BLOCK
\tleaq\tsegv(%rip), %rsi
\txorl\t%edx, %edx
\tmovl\t$8, %r10d
\tsyscall
\tmovq\t(%rsp), %rcx\t\t# argc
\tmovq\t16(%rsp), %rdi\t\t# argv[1], the command
\tleaq\t16(%rsp), %rsi\t\t# its arguments
\tleaq\t16(%rsp,%rcx,8), %rdx\t# the environment
\tmovl\t$59, %eax\t\t# execve
\tsyscall
\tmovl\t$127, %edi
\tmovl\t$60, %eax\t\t# exit
\tsyscall
\t.section\t.rodata
segv:\t.quad\t1 << 10
\t.section\t.note.GNU-stack,\"\",@progbits
";

/// A parent can leave SIGSEGV blocked when it runs the program. The runtime
/// unblocks it, so a run that outgrows its stack still says so.
#[test]
fn a_run_that_starts_with_sigsegv_blocked_still_reports_it_ran_out() {
    let exe = build("recursion-blocked", &recursive());
    let at = dir("recursion-blocking");
    let (source, object, launcher) = (at.join("b.s"), at.join("b.o"), at.join("b"));
    std::fs::write(&source, BLOCKING).unwrap();
    let ok = |cmd: &mut Command| {
        let out = cmd.output().unwrap();
        assert!(out.status.success(), "{}", text(&out.stderr));
    };
    ok(Command::new("as")
        .args(["--64", "-o"])
        .arg(&object)
        .arg(&source));
    ok(Command::new("ld")
        .args(["-m", "elf_x86_64", "-static", "-o"])
        .arg(&launcher)
        .arg(&object));
    let program = exe.display().to_string();
    let out = run_limited(LIMIT, &launcher, &[&program, "@forever", "0"]);
    ran_out(&out, &program, "@forever");
}

/// Recursion runs as deep as its stack allows: under the default limit far
/// deeper than the 16 KiB of slack that a stack sized from one frame had,
/// and with no stack limit deeper still.
#[test]
fn recursion_that_fits_its_stack_returns() {
    let exe = build("recursion-fits", &recursive());
    returned(&run_under(&DEFAULT, &exe, &["@count", "50000"]), "50000");
    returned(&run_under(&DEFAULT, &exe, &["@even", "50001"]), "false");
    returned(&run_under(&DEFAULT, &exe, &["@odd", "50001"]), "true");
    returned(
        &run_under(&UNLIMITED, &exe, &["@count", "200000"]),
        "200000",
    );
    returned(&run_under(&UNLIMITED, &exe, &["@even", "100001"]), "false");
    returned(&run_under(&UNLIMITED, &exe, &["@odd", "100001"]), "true");
}

/// A recursion that needs more stack than `ulimit -s` gives reports that
/// it ran out of exactly the limit, rounded down to a page, and returns
/// under a larger one. Each call of `@count` takes 80 bytes, so 50,000 of
/// them need about 4 MB and 200,000 about 16 MB.
#[test]
fn recursion_that_outgrows_a_small_stack_limit_runs_under_a_larger_one() {
    let exe = build("recursion-limits", &recursive());
    let program = exe.display().to_string();
    let out = run_under(&SMALL, &exe, &["@count", "50000"]);
    assert_eq!(ran_out(&out, &program, "@count"), SMALL_BYTES);
    let out = run_under(&ODD, &exe, &["@count", "50000"]);
    assert_eq!(ran_out(&out, &program, "@count"), ODD_BYTES);
    returned(&run_under(&DEFAULT, &exe, &["@count", "50000"]), "50000");
    let out = run_under(&DEFAULT, &exe, &["@count", "200000"]);
    assert_eq!(ran_out(&out, &program, "@count"), DEFAULT_BYTES);
    returned(&run_under(&LARGE, &exe, &["@count", "200000"]), "200000");
}

/// Kills the child when dropped, so that a failed test leaves no process
/// running.
struct Running(Child);

impl Drop for Running {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// Waits up to ten seconds for `check` to hold.
fn within_ten_seconds(what: &str, mut check: impl FnMut() -> bool) {
    let deadline = Instant::now() + Duration::from_secs(10);
    while !check() {
        assert!(Instant::now() < deadline, "{what}");
        std::thread::sleep(Duration::from_millis(5));
    }
}

/// The handler reports only a fault in the guard page. Any other SIGSEGV,
/// here one that another process sends, still ends the run by the signal.
#[test]
fn any_other_sigsegv_still_ends_the_run_by_the_signal() {
    let fir = module(&[
        "func @spin() -> i64 {\n^entry:\n  br ^loop @0\n^loop:\n  br ^loop @0\n}\n".into(),
    ]);
    let exe = build("recursion-spin", &fir);
    let mut run = Running(
        Command::new(&exe)
            .arg("@spin")
            .stdout(Stdio::piped())
            .spawn()
            .unwrap(),
    );
    let pid = run.0.id().to_string();
    // SIGSEGV is signal 11: bit 10 of the mask of the signals it catches.
    let caught = |s: String| {
        s.lines()
            .find_map(|l| l.strip_prefix("SigCgt:"))
            .and_then(|m| u64::from_str_radix(m.trim(), 16).ok())
            .is_some_and(|m| m & (1 << 10) != 0)
    };
    let status = format!("/proc/{pid}/status");
    within_ten_seconds("the run never catches SIGSEGV", || {
        std::fs::read_to_string(&status).is_ok_and(caught)
    });
    let sent = Command::new("sh")
        .args(["-c", "kill -s SEGV \"$0\"", &pid])
        .status()
        .unwrap();
    assert!(sent.success());
    let mut ended = None;
    within_ten_seconds("SIGSEGV does not end the run", || {
        ended = run.0.try_wait().unwrap();
        ended.is_some()
    });
    let mut stdout = String::new();
    run.0
        .stdout
        .take()
        .unwrap()
        .read_to_string(&mut stdout)
        .unwrap();
    assert_eq!(
        (ended.and_then(|s| s.signal()), stdout),
        (Some(11), String::new())
    );
}
