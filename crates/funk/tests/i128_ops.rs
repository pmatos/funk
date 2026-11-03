//! Every op that the backend lowers at `i128` (#21), run natively on
//! values that cross the 64-bit boundary and on the boundary bit patterns,
//! and checked against Rust's `i128` and `u128` arithmetic. Where the
//! source gives poison, from a broken flag or a shift by 128 or more, a
//! test asks only for a value of the type (ADR-2026-10-30-2248); everywhere
//! else it asks for the exact result.

mod common;

use common::{boundaries, build, expect, func, module, run, spell, text, wrap};
use funk_ir::dialects::core::WRAP_FLAG_SETS;

/// The boundary bit patterns of `i128`, values on either side of `2^63`
/// and `2^64` and their negations, and a value with every half distinct.
const VALUES: [i128; 14] = [
    0,
    1,
    -1,
    i128::MIN,
    i128::MAX,
    (1 << 63) - 1,
    1 << 63,
    -(1 << 63),
    -(1 << 63) - 1,
    (1 << 64) - 1,
    1 << 64,
    (1 << 64) + 1,
    -(1 << 64),
    0x0123_4567_89ab_cdef_fedc_ba98_7654_3210,
];

/// Runs `exe` with `args` and checks that it prints one value of `i128`,
/// whichever it is: the result where the source's is poison.
fn expect_some(exe: &std::path::Path, args: &[&str]) {
    let out = run(exe, args);
    let stdout = text(&out.stdout);
    let value = stdout
        .strip_prefix("{\"values\":[\"")
        .and_then(|s| s.strip_suffix("\"]}\n"));
    assert!(
        out.status.code() == Some(0)
            && out.stderr.is_empty()
            && value.is_some_and(|v| v.parse::<i128>().is_ok()),
        "{} {args:?}: {stdout}{}",
        exe.display(),
        text(&out.stderr)
    );
}

/// Checks one run: the exact result, or any value where it is poison.
fn check(exe: &std::path::Path, args: &[&str], result: Option<i128>) {
    match result {
        Some(r) => expect(exe, args, &[&r.to_string()]),
        None => expect_some(exe, args),
    }
}

/// `op` with `flags` on `a` and `b`: the wrapped result, or `None` when a
/// flag is broken, so that the result is poison.
fn arith(op: &str, flags: &[&str], a: i128, b: i128) -> Option<i128> {
    let (ua, ub) = (a as u128, b as u128);
    let (unsigned, signed, wrapped) = match op {
        "add" => (ua.checked_add(ub), a.checked_add(b), a.wrapping_add(b)),
        "sub" => (ua.checked_sub(ub), a.checked_sub(b), a.wrapping_sub(b)),
        "mul" => (ua.checked_mul(ub), a.checked_mul(b), a.wrapping_mul(b)),
        _ => panic!("no op {op}"),
    };
    let broken = (flags.contains(&"nuw") && unsigned.is_none())
        || (flags.contains(&"nsw") && signed.is_none());
    (!broken).then_some(wrapped)
}

/// A predicate of `icmp`, by name, and what it computes.
type Pred = (&'static str, fn(i128, i128) -> bool);

/// A bitwise op, by name, and what it computes.
type Bitwise = (&'static str, fn(i128, i128) -> i128);

/// A shift, by name, and what it computes for an amount below 128.
type Shift = (&'static str, fn(i128, u32) -> i128);

fn joined(op: &str, flags: &[&str], sep: &str) -> String {
    let words: Vec<&str> = std::iter::once(op).chain(flags.iter().copied()).collect();
    words.join(sep)
}

#[test]
fn add_sub_and_mul_carry_borrow_and_keep_the_high_half_of_products() {
    let ops = ["add", "sub", "mul"];
    let mut funcs = Vec::new();
    for op in ops {
        for fs in WRAP_FLAG_SETS {
            let line = format!("%r: i128 = {} %a, %b", joined(op, fs, " "));
            let name = joined(op, fs, "_");
            funcs.push(func(
                &name,
                "%a: i128, %b: i128",
                "i128",
                &[&line, "ret %r"],
            ));
        }
    }
    let exe = build("i128-arith", &module(&funcs));
    let mut poison = 0;
    for a in VALUES {
        for b in VALUES {
            let (sa, sb) = (a.to_string(), b.to_string());
            for op in ops {
                for fs in WRAP_FLAG_SETS {
                    let name = format!("@{}", joined(op, fs, "_"));
                    let r = arith(op, fs, a, b);
                    poison += usize::from(r.is_none());
                    check(&exe, &[&name, &sa, &sb], r);
                }
            }
        }
    }
    assert!(poison > 0, "no value breaks a flag");
}

#[test]
fn bitwise_ops_and_comparisons_read_both_halves() {
    let preds: [Pred; 10] = [
        ("eq", |a, b| a == b),
        ("ne", |a, b| a != b),
        ("slt", |a, b| a < b),
        ("sle", |a, b| a <= b),
        ("sgt", |a, b| a > b),
        ("sge", |a, b| a >= b),
        ("ult", |a, b| (a as u128) < (b as u128)),
        ("ule", |a, b| (a as u128) <= (b as u128)),
        ("ugt", |a, b| (a as u128) > (b as u128)),
        ("uge", |a, b| (a as u128) >= (b as u128)),
    ];
    let bitwise: [Bitwise; 3] = [
        ("and", |a, b| a & b),
        ("or", |a, b| a | b),
        ("xor", |a, b| a ^ b),
    ];
    let mut funcs = Vec::new();
    for (op, _) in bitwise {
        let line = format!("%r: i128 = {op} %a, %b");
        funcs.push(func(op, "%a: i128, %b: i128", "i128", &[&line, "ret %r"]));
    }
    for (p, _) in preds {
        let line = format!("%r: i1 = icmp {p} %a, %b");
        funcs.push(func(p, "%a: i128, %b: i128", "i1", &[&line, "ret %r"]));
    }
    let exe = build("i128-bitwise-icmp", &module(&funcs));
    for a in VALUES {
        for b in VALUES {
            let (sa, sb) = (a.to_string(), b.to_string());
            for (op, f) in bitwise {
                expect(
                    &exe,
                    &[&format!("@{op}"), &sa, &sb],
                    &[&f(a, b).to_string()],
                );
            }
            for (p, f) in preds {
                let want = if f(a, b) { "true" } else { "false" };
                expect(&exe, &[&format!("@{p}"), &sa, &sb], &[want]);
            }
        }
    }
}

/// Amounts below 64, at 64 and above, at 127, and of 128 or more, which
/// give poison, among them amounts whose low half is below 128.
const AMOUNTS: [i128; 15] = [
    0,
    1,
    63,
    64,
    65,
    127,
    128,
    129,
    255,
    256,
    1 << 64,
    (1 << 64) + 1,
    -1,
    i128::MIN,
    i128::MAX,
];

#[test]
fn shifts_cross_the_halves_and_give_poison_at_128_or_more() {
    let shifts: [Shift; 3] = [
        ("shl", |a, n| ((a as u128) << n) as i128),
        ("lshr", |a, n| ((a as u128) >> n) as i128),
        ("ashr", |a, n| a >> n),
    ];
    let funcs: Vec<String> = shifts
        .iter()
        .map(|(op, _)| {
            let line = format!("%r: i128 = {op} %a, %n");
            func(op, "%a: i128, %n: i128", "i128", &[&line, "ret %r"])
        })
        .collect();
    let exe = build("i128-shift", &module(&funcs));
    for a in VALUES {
        for n in AMOUNTS {
            for (op, f) in shifts {
                let r = u32::try_from(n).ok().filter(|&n| n < 128).map(|n| f(a, n));
                check(
                    &exe,
                    &[&format!("@{op}"), &a.to_string(), &n.to_string()],
                    r,
                );
            }
        }
    }
}

#[test]
fn select_chooses_both_halves() {
    let line = "%r: i128 = select %c, %a, %b";
    let f = func(
        "sel",
        "%c: i1, %a: i128, %b: i128",
        "i128",
        &[line, "ret %r"],
    );
    let exe = build("i128-select", &module(&[f]));
    for a in VALUES {
        for b in VALUES {
            for (c, r) in [("true", a), ("false", b)] {
                expect(
                    &exe,
                    &["@sel", c, &a.to_string(), &b.to_string()],
                    &[&r.to_string()],
                );
            }
        }
    }
}

#[test]
fn width_changes_go_to_and_from_i128() {
    let narrow = [1, 8, 16, 32, 64];
    let mut funcs = Vec::new();
    for m in narrow {
        let t = format!("i{m}");
        for op in ["zext", "sext"] {
            let line = format!("%r: i128 = {op} %a");
            funcs.push(func(
                &format!("{op}{m}"),
                &format!("%a: {t}"),
                "i128",
                &[&line, "ret %r"],
            ));
        }
        let line = format!("%r: {t} = trunc %a");
        funcs.push(func(
            &format!("trunc{m}"),
            "%a: i128",
            &t,
            &[&line, "ret %r"],
        ));
    }
    let exe = build("i128-width", &module(&funcs));
    for m in narrow {
        for v in boundaries(m) {
            let unsigned = v.rem_euclid(1i128 << m);
            for (op, r) in [("zext", unsigned), ("sext", v)] {
                let name = format!("@{op}{m}");
                expect(&exe, &[&name, &spell(m, v)], &[&r.to_string()]);
            }
        }
        for v in VALUES {
            let name = format!("@trunc{m}");
            expect(&exe, &[&name, &v.to_string()], &[&spell(m, wrap(m, v))]);
        }
    }
}

/// `%p` is `add nsw %a, 1`, poison on the maximum. A frozen value is one
/// value, both halves of it: `xor %f, %f` and `sub %f, %f` give 0, and
/// the high half that one use reads is the one that another reads.
#[test]
fn freeze_keeps_both_halves_of_one_value() {
    let p = [
        "%one: i128 = const 1",
        "%p: i128 = add nsw %a, %one",
        "%f: i128 = freeze %p",
    ];
    let with =
        |ops: &[&str]| -> Vec<String> { p.iter().chain(ops).map(|s| s.to_string()).collect() };
    let body = |name: &str, ops: &[&str]| {
        let lines = with(ops);
        let refs: Vec<&str> = lines.iter().map(String::as_str).collect();
        func(name, "%a: i128", "i128", &refs)
    };
    let funcs = [
        body("keep", &["ret %f"]),
        body("xor", &["%d: i128 = xor %f, %f", "ret %d"]),
        body("sub", &["%d: i128 = sub %f, %f", "ret %d"]),
        body(
            "halves",
            &[
                "%k: i128 = const 64",
                "%h: i128 = lshr %f, %k",
                "%g: i128 = shl %f, %k",
                "%l: i128 = lshr %g, %k",
                "%hi: i128 = shl %h, %k",
                "%w: i128 = or %hi, %l",
                "%d: i128 = xor %w, %f",
                "ret %d",
            ],
        ),
    ];
    let exe = build("i128-freeze", &module(&funcs));
    for a in VALUES {
        let sa = a.to_string();
        check(&exe, &["@keep", &sa], a.checked_add(1));
        for f in ["@xor", "@sub", "@halves"] {
            expect(&exe, &[f, &sa], &["0"]);
        }
    }
}

#[test]
fn constants_are_both_halves_of_their_value() {
    let funcs: Vec<String> = VALUES
        .iter()
        .enumerate()
        .map(|(k, v)| {
            let line = format!("%c: i128 = const {v}");
            func(&format!("c{k}"), "", "i128", &[&line, "ret %c"])
        })
        .collect();
    let exe = build("i128-const", &module(&funcs));
    for (k, v) in VALUES.iter().enumerate() {
        expect(&exe, &[&format!("@c{k}")], &[&v.to_string()]);
    }
}

#[test]
fn division_at_i128_is_not_lowered_yet() {
    for op in ["sdiv", "udiv", "srem", "urem"] {
        let line = format!("%r: i128 = {op} %a, %b");
        let text = module(&[func("d", "%a: i128, %b: i128", "i128", &[&line, "ret %r"])]);
        let (out, _, _) = common::try_build(&format!("i128-{op}"), &text, &[]);
        assert_eq!(out.status.code(), Some(1));
        let err = common::text(&out.stderr);
        assert!(
            err.contains(&format!(
                "unsupported in @d ^entry op 0: %r: the x86-64 backend does not lower {op} at \
                 i128 yet"
            )),
            "{err}"
        );
    }
}
