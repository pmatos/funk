//! Division at `i128` (#22) among several results, as a call's argument and
//! result, and in recursion, run natively and checked against Rust's `i128`
//! and `u128` arithmetic; a module whose functions have the names of the
//! helper's routines
//! (`docs/decisions/x86-64-backend-lowering.md#division-at-i128`); two
//! object files that both carry the helper, linked into one program; and
//! the widths at which the backend divides.

mod common;

use std::process::Command;

use common::{build, expect, func, module, run, text, try_build};

/// Dividends and divisors of both signs, across `2^64`, near the signed
/// minimum, and with no UB between any two: no zero, and no `-1` next to
/// the signed minimum.
const VALUES: [i128; 9] = [
    1,
    -7,
    100,
    i128::MIN,
    i128::MIN + 1,
    i128::MAX,
    (1 << 64) + 3,
    -(1 << 64) - 1,
    0x0123_4567_89ab_cdef_fedc_ba98_7654_3210,
];

fn strings(vs: &[i128]) -> Vec<String> {
    vs.iter().map(i128::to_string).collect()
}

fn refs(vs: &[String]) -> Vec<&str> {
    vs.iter().map(String::as_str).collect()
}

/// `@divmod` returns its quotient and remainder, two `i128`s, and
/// `@udivmod3` returns `i128, i64, i128`: four and five eightbytes, so
/// both go in the caller's result area (ADR-2026-10-30-1232). Callers pass
/// the results on, as arguments and as results, and `@recompose`
/// multiplies them back into the dividend.
#[test]
fn division_works_among_several_results_and_across_calls() {
    let funcs = [
        func(
            "divmod",
            "%a: i128, %b: i128",
            "i128, i128",
            &[
                "%q: i128 = sdiv %a, %b",
                "%r: i128 = srem %a, %b",
                "ret %q, %r",
            ],
        ),
        func(
            "udivmod3",
            "%a: i128, %b: i128",
            "i128, i64, i128",
            &[
                "%q: i128 = udiv %a, %b",
                "%r: i128 = urem %a, %b",
                "%t: i64 = trunc %r",
                "ret %q, %t, %r",
            ],
        ),
        func(
            "recompose",
            "%a: i128, %b: i128",
            "i128",
            &[
                "%q: i128, %r: i128 = call @divmod %a, %b",
                "%m: i128 = mul %q, %b",
                "%s: i128 = add %m, %r",
                "ret %s",
            ],
        ),
        func(
            "nested",
            "%a: i128, %b: i128, %c: i128",
            "i64, i128",
            &[
                "%q: i128 = sdiv %a, %b",
                "%x: i128, %t: i64, %y: i128 = call @udivmod3 %q, %c",
                "%z: i128 = srem %y, %c",
                "ret %t, %z",
            ],
        ),
    ];
    let exe = build("i128-div-results", &module(&funcs));
    let mut runs = 0;
    for a in VALUES {
        for b in VALUES {
            let (ua, ub) = (a as u128, b as u128);
            let args = strings(&[a, b]);
            let args = refs(&args);
            let pair = strings(&[a / b, a % b]);
            expect(&exe, &[&["@divmod"], &args[..]].concat(), &refs(&pair));
            expect(&exe, &[&["@recompose"], &args[..]].concat(), &[args[0]]);
            let r = (ua % ub) as i128;
            let three = strings(&[(ua / ub) as i128, i128::from(r as i64), r]);
            expect(&exe, &[&["@udivmod3"], &args[..]].concat(), &refs(&three));
            for c in VALUES {
                let (q, uc) = ((a / b) as u128, c as u128);
                let r = (q % uc) as i128;
                let want = strings(&[i128::from(r as i64), r % c]);
                let all = strings(&[a, b, c]);
                expect(
                    &exe,
                    &[&["@nested"], &refs(&all)[..]].concat(),
                    &refs(&want),
                );
                runs += 1;
            }
        }
    }
    assert_eq!(runs, VALUES.len().pow(3));
}

/// `@digits` counts the decimal digits of an unsigned `i128` by dividing
/// it by 10 and recursing, up to 39 deep, and `@up` rebuilds a value from
/// its last digit and the recursion's quotient.
#[test]
fn division_works_in_recursion() {
    let funcs = [
        func(
            "digits",
            "%x: i128",
            "i128",
            &[
                "%ten: i128 = const 10",
                "%one: i128 = const 1",
                "%small: i1 = icmp ult %x, %ten",
                "cond_br %small, ^done, ^more",
                "^done:",
                "ret %one",
                "^more:",
                "%q: i128 = udiv %x, %ten",
                "%n: i128 = call @digits %q",
                "%m: i128 = add %n, %one",
                "ret %m",
            ],
        )
        .replace("  ^done: @0\n", "^done:\n")
        .replace("  ^more: @0\n", "^more:\n"),
        func(
            "up",
            "%x: i128",
            "i128",
            &[
                "%ten: i128 = const 10",
                "%zero: i128 = const 0",
                "%end: i1 = icmp eq %x, %zero",
                "cond_br %end, ^done, ^more",
                "^done:",
                "ret %zero",
                "^more:",
                "%q: i128 = sdiv %x, %ten",
                "%d: i128 = srem %x, %ten",
                "%h: i128 = call @up %q",
                "%s: i128 = mul %h, %ten",
                "%t: i128 = add %s, %d",
                "ret %t",
            ],
        )
        .replace("  ^done: @0\n", "^done:\n")
        .replace("  ^more: @0\n", "^more:\n"),
    ];
    let exe = build("i128-div-recursion", &module(&funcs));
    for v in [
        0,
        9,
        10,
        99,
        i128::MAX,
        -1,
        i128::MIN,
        10i128.pow(38),
        -12345,
    ] {
        let digits = (v as u128).to_string().len();
        expect(&exe, &["@digits", &v.to_string()], &[&digits.to_string()]);
        expect(&exe, &["@up", &v.to_string()], &[&v.to_string()]);
    }
}

/// Functions named as two of the helper's routines, words that start with
/// `_`, and as one of its labels, which fir quotes, keep symbols of their
/// own: each divides through the helper and gives what its own body says,
/// and a division in another function still calls the helper, not them.
#[test]
fn functions_with_the_helper_s_names_build_and_run() {
    let body = |name: &str, ops: &[&str]| {
        let mut lines = vec!["%q: i128 = sdiv %a, %b"];
        lines.extend(ops);
        func(name, "%a: i128, %b: i128", "i128", &lines)
    };
    let funcs = [
        body(
            "__funk_rt_sdiv128",
            &["%one: i128 = const 1", "%r: i128 = add %q, %one", "ret %r"],
        ),
        body(
            "__funk_rt_udivmod128",
            &["%r: i128 = urem %a, %b", "%s: i128 = sub %q, %r", "ret %s"],
        ),
        body(
            "\".Lrt_div128_step\"",
            &["%k: i128 = const 99", "%r: i128 = xor %q, %k", "ret %r"],
        ),
        body("plain", &["ret %q"]),
        func(
            "via",
            "%a: i128, %b: i128",
            "i128",
            &[
                "%x: i128 = call @__funk_rt_sdiv128 %a, %b",
                "%y: i128 = call @__funk_rt_udivmod128 %a, %b",
                "%z: i128 = call @\".Lrt_div128_step\" %a, %b",
                "%s: i128 = add %x, %y",
                "%t: i128 = add %s, %z",
                "ret %t",
            ],
        ),
    ];
    let exe = build("i128-div-names", &module(&funcs));
    for (a, b) in [
        (100i128, 7i128),
        (-(1 << 100), (1 << 64) + 1),
        (i128::MAX, -3),
    ] {
        let (q, ur) = (a / b, ((a as u128) % (b as u128)) as i128);
        let (one, two, three) = (q + 1, q.wrapping_sub(ur), q ^ 99);
        let args = strings(&[a, b]);
        for (name, want) in [
            ("@__funk_rt_sdiv128", one),
            ("@__funk_rt_udivmod128", two),
            ("@\".Lrt_div128_step\"", three),
            ("@plain", q),
            ("@via", one.wrapping_add(two).wrapping_add(three)),
        ] {
            expect(&exe, &[name, &args[0], &args[1]], &[&want.to_string()]);
        }
    }
}

/// A program that calls `@qa` and `@qb` from two object files that each
/// carry the helper, and exits with 0 when both results are right.
fn start(urem: u128) -> String {
    let (lo, hi) = (urem as u64, (urem >> 64) as u64);
    format!(
        "\t.text\n\t.globl\t_start\n_start:\n\
         \tmovq\t$-100, %rdi\n\tmovq\t$-1, %rsi\n\tmovl\t$7, %edx\n\txorl\t%ecx, %ecx\n\
         \tcall\tqa\n\tcmpq\t$-14, %rax\n\tjne\t1f\n\tcmpq\t$-1, %rdx\n\tjne\t1f\n\
         \tmovl\t$5, %edi\n\tmovabsq\t${}, %rsi\n\tmovl\t$3, %edx\n\tmovl\t$1, %ecx\n\
         \tcall\tqb\n\tmovabsq\t${lo}, %r8\n\tcmpq\t%r8, %rax\n\tjne\t1f\n\
         \tmovabsq\t${hi}, %r8\n\tcmpq\t%r8, %rdx\n\tjne\t1f\n\
         \txorl\t%edi, %edi\n\tmovl\t$231, %eax\n\tsyscall\n\
         1:\tmovl\t$1, %edi\n\tmovl\t$231, %eax\n\tsyscall\n\
         \t.section\t.note.GNU-stack,\"\",@progbits\n",
        1u64 << 36
    )
}

/// Each object file holds the helper under local symbols, so a program
/// links both with `ld` and no runtime of its own, and each function
/// calls its own copy
/// (`docs/decisions/x86-64-backend-lowering.md#division-at-i128`).
#[test]
fn two_object_files_with_the_helper_link_into_one_program() {
    let qa = func(
        "qa",
        "%a: i128, %b: i128",
        "i128",
        &["%r: i128 = sdiv %a, %b", "ret %r"],
    );
    let qb = func(
        "qb",
        "%a: i128, %b: i128",
        "i128",
        &["%r: i128 = urem %a, %b", "ret %r"],
    );
    let a = build("i128-div-link-a", &module(&[qa]));
    let b = build("i128-div-link-b", &module(&[qb]));
    let dir = common::dir("i128-div-link");
    let (source, object, program) = (dir.join("s.s"), dir.join("s.o"), dir.join("s"));
    let urem = ((1u128 << 100) + 5) % ((1u128 << 64) + 3);
    std::fs::write(&source, start(urem)).unwrap();
    let ok = |cmd: &mut Command| {
        let out = cmd.output().unwrap();
        assert!(
            out.status.success() && out.stderr.is_empty(),
            "{}",
            text(&out.stderr)
        );
    };
    ok(Command::new("as")
        .args(["--64", "-o"])
        .arg(&object)
        .arg(&source));
    let objects = [a, b].map(|exe| format!("{}.o", exe.display()));
    ok(Command::new("ld")
        .args(["-m", "elf_x86_64", "-static", "-o"])
        .arg(&program)
        .arg(&object)
        .args(&objects));
    let out = run(&program, &[]);
    assert_eq!(out.status.code(), Some(0));
}

/// The backend divides at each width it lowers, `i128` included, and
/// reports a division at any other width only by the width of its values.
#[test]
fn division_is_lowered_at_every_width_of_the_backend() {
    let mut funcs = Vec::new();
    for w in [1, 8, 16, 32, 64, 128] {
        for op in ["sdiv", "udiv exact", "srem", "urem"] {
            let name = format!("{}{w}", op.replace(' ', "_"));
            let line = format!("%r: i{w} = {op} %a, %b");
            let params = format!("%a: i{w}, %b: i{w}");
            funcs.push(func(&name, &params, &format!("i{w}"), &[&line, "ret %r"]));
        }
    }
    build("i128-div-widths", &module(&funcs));
    for w in [7, 33, 65, 127, 129, 256] {
        let line = format!("%r: i{w} = sdiv %a, %b");
        let params = format!("%a: i{w}, %b: i{w}");
        let f = func("d", &params, &format!("i{w}"), &[&line, "ret %r"]);
        let (out, _, _) = try_build(&format!("i128-div-i{w}"), &module(&[f]), &[]);
        assert_eq!(out.status.code(), Some(1));
        let err = text(&out.stderr);
        let not =
            format!("the x86-64 backend lowers i1, i8, i16, i32, i64, i128, f32 and f64, not i{w}");
        assert_eq!(err.matches(&not).count(), 3, "{err}");
        assert_eq!(err.lines().count(), 3, "{err}");
    }
}
