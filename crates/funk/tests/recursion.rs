//! The stack of a recursive run (ADR-2026-11-02-1132): it gets as much
//! stack as memory allows, so recursion goes deep, and a run that outgrows
//! its stack says so in one line, with exit status 2.
//!
//! A run that recurses without end is only ever made under `ulimit -d`, a
//! limit on the data a process maps, and `ulimit -v`, which binds even on a
//! kernel that ignores the first. Without them its stack would be as large
//! as the machine's memory and swap, and the run would use them all before
//! it reached the end.

#![cfg(unix)]

mod common;

use std::io::Read;
use std::os::unix::process::ExitStatusExt;
use std::path::Path;
use std::process::{Child, Command, Output, Stdio};
use std::time::{Duration, Instant};

use common::{build, dir, expect, module, text, values};

/// The limit, in KiB, under which runs that never end are made: 64 MiB.
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

/// Runs `exe` with `args` after `sh` limits the data it maps to `kib` KiB,
/// and its address space to 16 MiB more.
fn run_limited(kib: u64, exe: &Path, args: &[&str]) -> Output {
    let space = kib + 16 * 1024;
    Command::new("sh")
        .arg("-c")
        .arg(format!(
            "ulimit -d {kib} && ulimit -v {space} && exec \"$0\" \"$@\""
        ))
        .arg(exe)
        .args(args)
        .output()
        .unwrap()
}

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

/// The runtime halves the stack it asks for until the kernel grants it, so
/// each run's stack is more than a quarter of the limit, and less than all.
#[test]
fn a_run_that_recurses_without_end_reports_that_it_ran_out_of_stack() {
    let exe = build("recursion-forever", &recursive());
    let program = exe.display().to_string();
    let limit = LIMIT * 1024;
    for name in ["@forever", "@ping", "@pong", "@outer", "@\"for ever\""] {
        let bytes = ran_out(&run_limited(LIMIT, &exe, &[name, "0"]), &program, name);
        assert!(
            bytes.is_multiple_of(4096) && bytes > limit / 4 && bytes < limit,
            "{bytes}"
        );
    }
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

/// Recursion runs as deep as its stack allows: here far deeper than the
/// 16 KiB of slack that a stack sized from one frame had, under the limit
/// too, and under a limit of 1 MiB, which leaves a smaller stack.
#[test]
fn recursion_that_fits_its_stack_returns() {
    let exe = build("recursion-fits", &recursive());
    expect(&exe, &["@count", "200000"], &["200000"]);
    expect(&exe, &["@even", "100001"], &["false"]);
    expect(&exe, &["@odd", "100001"], &["true"]);
    let limited = |kib, n: &str| {
        let out = run_limited(kib, &exe, &["@count", n]);
        assert_eq!(
            (out.status.code(), text(&out.stdout), text(&out.stderr)),
            (Some(0), values(&[n]), String::new())
        );
    };
    limited(LIMIT, "200000");
    limited(1024, "1000");
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
