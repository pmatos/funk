//! `i128` among several results (#21, #31), run natively and checked
//! against Rust's `i128` arithmetic. A function returns its results as
//! System V returns a structure (ADR-2026-11-03-0109): one `i128` alone in
//! `%rdx:%rax`, and next to any other result in the caller's result area,
//! at an offset that is a multiple of 16, its low half first. The area's
//! address is the call's first argument, so an `i128` argument may find no
//! pair of registers left and go on the stack (ADR-2026-11-03-0108).

mod common;

use std::path::Path;

use common::{boundaries, build, expect, module, run, spell, text, wrap};

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

/// What `@spillN` folds its arguments with: multiply, then add the next.
const K: i128 = 1_000_003;

/// The text of `func @name(params) -> results` with the lines `lines`: an
/// op at `@0`, or a block's label, which starts with `^`.
fn func(name: &str, params: &str, results: &str, lines: &[String]) -> String {
    let mut text = format!("func @{name}({params}) -> {results} {{\n^entry:\n");
    for l in lines {
        if l.starts_with('^') {
            text.push_str(&format!("{l}\n"));
        } else {
            text.push_str(&format!("  {l} @0\n"));
        }
    }
    text + "}\n"
}

/// `%p0: iW0, %p1: iW1, ...`.
fn params(ws: &[u32]) -> String {
    let ps: Vec<String> = ws
        .iter()
        .enumerate()
        .map(|(k, w)| format!("%p{k}: i{w}"))
        .collect();
    ps.join(", ")
}

/// `iW0, iW1, ...`.
fn types(ws: &[u32]) -> String {
    let ts: Vec<String> = ws.iter().map(|w| format!("i{w}")).collect();
    ts.join(", ")
}

/// `x + 1` at `iW`, wrapped.
fn inc(w: u32, x: i128) -> i128 {
    if w == 128 {
        x.wrapping_add(1)
    } else {
        wrap(w, x + 1)
    }
}

/// The value of `iW` that parameter `k` takes in run `r`: each width runs
/// through its boundary values, and `i128` through [`VALUES`].
fn value(w: u32, k: usize, r: usize) -> i128 {
    if w == 128 {
        VALUES[(k * 5 + r) % VALUES.len()]
    } else {
        let b = boundaries(w);
        b[(k + r) % b.len()]
    }
}

/// Runs `@name` on `vs`, of the widths `ws`, and checks that it prints
/// `want`, of the widths `outs`.
fn check(exe: &Path, name: &str, ws: &[u32], vs: &[i128], outs: &[u32], want: &[i128]) {
    let args: Vec<String> = ws.iter().zip(vs).map(|(&w, &v)| spell(w, v)).collect();
    let mut argv = vec![name];
    argv.extend(args.iter().map(String::as_str));
    let want: Vec<String> = outs.iter().zip(want).map(|(&w, &v)| spell(w, v)).collect();
    let want: Vec<&str> = want.iter().map(String::as_str).collect();
    expect(exe, &argv, &want);
}

/// Result lists with an `i128` first, in the middle, last, next to an
/// `i64` in either order, twice, among three narrower results, twice among
/// narrower ones, and alone.
const SHAPES: [&[u32]; 9] = [
    &[128, 8, 1],
    &[1, 128, 8],
    &[64, 16, 128],
    &[128, 64],
    &[64, 128],
    &[128, 128],
    &[1, 128, 8, 16],
    &[128, 32, 128, 1],
    &[128],
];

/// `@retN`, which returns each of its parameters, of the widths `ws`, plus
/// one, and `@useN`, which calls it and returns its results reversed, each
/// plus one again.
fn shape(n: usize, ws: &[u32]) -> [String; 2] {
    let one = |w: u32| if w == 1 { "true" } else { "1" };
    let mut ret = Vec::new();
    for (k, &w) in ws.iter().enumerate() {
        ret.push(format!("%c{k}: i{w} = const {}", one(w)));
        ret.push(format!("%r{k}: i{w} = add %p{k}, %c{k}"));
    }
    let rs: Vec<String> = (0..ws.len()).map(|k| format!("%r{k}")).collect();
    ret.push(format!("ret {}", rs.join(", ")));
    let defs: Vec<String> = ws
        .iter()
        .enumerate()
        .map(|(k, w)| format!("%r{k}: i{w}"))
        .collect();
    let ps: Vec<String> = (0..ws.len()).map(|k| format!("%p{k}")).collect();
    let mut caller = vec![format!(
        "{} = call @ret{n} {}",
        defs.join(", "),
        ps.join(", ")
    )];
    for (k, &w) in ws.iter().enumerate() {
        caller.push(format!("%c{k}: i{w} = const {}", one(w)));
        caller.push(format!("%s{k}: i{w} = add %r{k}, %c{k}"));
    }
    let ss: Vec<String> = (0..ws.len()).rev().map(|k| format!("%s{k}")).collect();
    caller.push(format!("ret {}", ss.join(", ")));
    let rev: Vec<u32> = ws.iter().rev().copied().collect();
    [
        func(&format!("ret{n}"), &params(ws), &types(ws), &ret),
        func(&format!("use{n}"), &params(ws), &types(&rev), &caller),
    ]
}

fn shapes() -> Vec<String> {
    SHAPES
        .iter()
        .enumerate()
        .flat_map(|(n, ws)| shape(n, ws))
        .collect()
}

#[test]
fn an_i128_result_comes_back_wherever_it_is_among_others() {
    let exe = build("i128-results", &module(&shapes()));
    for (n, ws) in SHAPES.iter().enumerate() {
        let rev: Vec<u32> = ws.iter().rev().copied().collect();
        for r in 0..VALUES.len() {
            let vs: Vec<i128> = ws
                .iter()
                .enumerate()
                .map(|(k, &w)| value(w, k, r))
                .collect();
            let once: Vec<i128> = ws.iter().zip(&vs).map(|(&w, &v)| inc(w, v)).collect();
            check(&exe, &format!("@ret{n}"), ws, &vs, ws, &once);
            let twice: Vec<i128> = ws
                .iter()
                .zip(&once)
                .map(|(&w, &v)| inc(w, v))
                .rev()
                .collect();
            check(&exe, &format!("@use{n}"), ws, &vs, &rev, &twice);
        }
    }
}

/// `@chain` passes an `i128` result of one call on to the next, as an
/// argument and next to other results: `@ret3` gives `x + 1` and `a + 1`,
/// `@ret4` `a + 2` and `x + 2`, and `@ret5` `x + 3` and `x + 2`.
#[test]
fn an_i128_result_passes_on_as_an_argument_and_among_results() {
    let chain = func(
        "chain",
        "%x: i128, %a: i64",
        "i64, i128, i128",
        &[
            "%p: i128, %q: i64 = call @ret3 %x, %a".into(),
            "%r: i64, %s: i128 = call @ret4 %q, %p".into(),
            "%t: i128, %u: i128 = call @ret5 %s, %p".into(),
            "ret %r, %t, %u".into(),
        ],
    );
    let mut funcs = shapes();
    funcs.push(chain);
    let exe = build("i128-results-chain", &module(&funcs));
    for (r, &x) in VALUES.iter().enumerate() {
        let a = value(64, 1, r);
        let want = [wrap(64, a + 2), x.wrapping_add(3), x.wrapping_add(2)];
        check(&exe, "@chain", &[128, 64], &[x, a], &[64, 128, 128], &want);
    }
}

/// Parameter lists of calls whose results go in memory, so that the
/// area's address takes `%rdi`: an `i128` after four `i64`s finds only
/// `%r9` left; three `i128`s fill `%rsi` to `%r8`, and the third goes on
/// the stack; an `i64` and three `i128`s, five `i64`s and an `i128`, two
/// `i128`s, an `i64` and an `i128`; six `i64`s, so that an `i128` after
/// them goes on the stack past a hole; and a mix of widths.
const SPILLS: [&[u32]; 7] = [
    &[64, 64, 64, 64, 128],
    &[128, 128, 128],
    &[64, 128, 128, 128],
    &[64, 64, 64, 64, 64, 128],
    &[128, 128, 64, 128],
    &[64, 64, 64, 64, 64, 64, 128, 64],
    &[1, 128, 16, 128, 32, 128, 64, 128],
];

/// `@spillN`, which folds its parameters, of the widths `ws` reversed,
/// and returns the fold, its low 8 bits and its last `i128` parameter; and
/// `@spill_callN`, which adds one to each of its parameters, of the widths
/// `ws`, passes them to it in reverse order, and returns its last `i128`,
/// the `i8` and the sum of the two `i128`s. So the two lay out different
/// lists, each after the area's address.
fn spill(n: usize, ws: &[u32]) -> [String; 2] {
    let rev: Vec<u32> = ws.iter().rev().copied().collect();
    let mut callee = vec![
        "%acc0: i128 = const 0".to_string(),
        format!("%k: i128 = const {K}"),
    ];
    let mut last = String::new();
    for (k, w) in rev.iter().enumerate() {
        let x = if *w == 128 {
            last = format!("%p{k}");
            format!("%p{k}")
        } else {
            callee.push(format!("%x{k}: i128 = sext %p{k}"));
            format!("%x{k}")
        };
        callee.push(format!("%m{k}: i128 = mul %acc{k}, %k"));
        callee.push(format!("%acc{}: i128 = add %m{k}, {x}", k + 1));
    }
    let acc = format!("%acc{}", rev.len());
    callee.push(format!("%t: i8 = trunc {acc}"));
    callee.push(format!("ret {acc}, %t, {last}"));
    let mut caller = Vec::new();
    for (k, w) in ws.iter().enumerate() {
        let one = if *w == 1 { "true" } else { "1" };
        caller.push(format!("%one{k}: i{w} = const {one}"));
        caller.push(format!("%q{k}: i{w} = add %p{k}, %one{k}"));
    }
    let args: Vec<String> = (0..ws.len()).rev().map(|k| format!("%q{k}")).collect();
    caller.push(format!(
        "%a: i128, %t: i8, %l: i128 = call @spill{n} {}",
        args.join(", ")
    ));
    caller.push("%s: i128 = add %a, %l".into());
    caller.push("ret %l, %t, %s".into());
    [
        func(
            &format!("spill{n}"),
            &params(&rev),
            "i128, i8, i128",
            &callee,
        ),
        func(
            &format!("spill_call{n}"),
            &params(ws),
            "i128, i8, i128",
            &caller,
        ),
    ]
}

/// What `@spillN` returns for `vs`, of the widths `ws`, in its order.
fn folded(ws: &[u32], vs: &[i128]) -> [i128; 3] {
    let acc = vs
        .iter()
        .fold(0i128, |a, &x| a.wrapping_mul(K).wrapping_add(x));
    let last = ws.iter().zip(vs).rfind(|&(&w, _)| w == 128);
    [acc, wrap(8, acc & 0xff), *last.unwrap().1]
}

#[test]
fn the_area_s_address_moves_i128_arguments_to_the_stack() {
    let funcs: Vec<String> = SPILLS
        .iter()
        .enumerate()
        .flat_map(|(n, ws)| spill(n, ws))
        .collect();
    let exe = build("i128-results-spill", &module(&funcs));
    for (n, ws) in SPILLS.iter().enumerate() {
        let rev: Vec<u32> = ws.iter().rev().copied().collect();
        for r in 0..VALUES.len() {
            let vs: Vec<i128> = ws
                .iter()
                .enumerate()
                .map(|(k, &w)| value(w, k, r))
                .collect();
            let rvs: Vec<i128> = vs.iter().rev().copied().collect();
            let outs = [128, 8, 128];
            check(
                &exe,
                &format!("@spill{n}"),
                &rev,
                &rvs,
                &outs,
                &folded(&rev, &rvs),
            );
            let plus: Vec<i128> = rev.iter().zip(&rvs).map(|(&w, &v)| inc(w, v)).collect();
            let [acc, t, last] = folded(&rev, &plus);
            let want = [last, t, acc.wrapping_add(last)];
            check(&exe, &format!("@spill_call{n}"), ws, &vs, &outs, &want);
        }
    }
}

/// `@fibs` steps `(a, b)` to `(b, a + b)` `n` times by calling itself on
/// `n - 1`, and returns the pair around how many steps it took. Each call
/// passes two `i128`s in registers after the area's address and returns
/// two in the area, 20 deep at most.
#[test]
fn recursion_returns_i128s_among_several_results() {
    let fibs = func(
        "fibs",
        "%n: i64, %a: i128, %b: i128",
        "i128, i64, i128",
        &[
            "%zero: i64 = const 0".into(),
            "%done: i1 = icmp sle %n, %zero".into(),
            "cond_br %done, ^base, ^step".into(),
            "^base:".into(),
            "ret %a, %n, %b".into(),
            "^step:".into(),
            "%one: i64 = const 1".into(),
            "%m: i64 = sub %n, %one".into(),
            "%c: i128 = add %a, %b".into(),
            "%x: i128, %k: i64, %y: i128 = call @fibs %m, %b, %c".into(),
            "%k1: i64 = add %k, %one".into(),
            "ret %x, %k1, %y".into(),
        ],
    );
    let exe = build("i128-results-fibs", &module(&[fibs]));
    for s in [1, (1 << 64) + 3, 1 << 63, -1, i128::MAX] {
        let (mut a, mut b) = (0i128, s);
        for n in 0..=20i128 {
            let want = [a, n, b];
            check(
                &exe,
                "@fibs",
                &[64, 128, 128],
                &[n, 0, s],
                &[128, 64, 128],
                &want,
            );
            (a, b) = (b, a.wrapping_add(b));
        }
    }
}

/// Runs `exe` with `args` and returns the values it prints.
fn values(exe: &Path, args: &[&str]) -> Vec<String> {
    let out = run(exe, args);
    let stdout = text(&out.stdout);
    assert!(
        out.status.code() == Some(0) && out.stderr.is_empty(),
        "{stdout}"
    );
    let inner = stdout
        .strip_prefix("{\"values\":[\"")
        .and_then(|s| s.strip_suffix("\"]}\n"))
        .unwrap_or_else(|| panic!("{stdout}"));
    inner.split("\",\"").map(str::to_string).collect()
}

/// Native code holds no poison: `@poison` returns `x + 1` with `nsw`,
/// some `i128` when that overflows, between two defined results, and
/// `@frozen` a frozen `x + max` twice, which must be one value in both
/// places of the area, as `@frozen_use` checks.
#[test]
fn poison_and_a_frozen_value_among_i128_results() {
    let poison = func(
        "poison",
        "%x: i128, %a: i8",
        "i8, i128, i1",
        &[
            "%one: i128 = const 1".into(),
            "%p: i128 = add nsw %x, %one".into(),
            "%t: i1 = const true".into(),
            "ret %a, %p, %t".into(),
        ],
    );
    let frozen = func(
        "frozen",
        "%x: i128",
        "i128, i8, i128",
        &[
            format!("%big: i128 = const {}", i128::MAX),
            "%p: i128 = add nsw %x, %big".into(),
            "%f: i128 = freeze %p".into(),
            "%c: i8 = const 7".into(),
            "ret %f, %c, %f".into(),
        ],
    );
    let frozen_use = func(
        "frozen_use",
        "%x: i128",
        "i128, i8",
        &[
            "%a: i128, %c: i8, %b: i128 = call @frozen %x".into(),
            "%d: i128 = sub %a, %b".into(),
            "ret %d, %c".into(),
        ],
    );
    let exe = build(
        "i128-results-poison",
        &module(&[poison, frozen, frozen_use]),
    );
    for (r, &x) in VALUES.iter().enumerate() {
        let a = value(8, 0, r);
        let vs = values(&exe, &["@poison", &x.to_string(), &a.to_string()]);
        assert_eq!(
            (vs[0].as_str(), vs[2].as_str()),
            (a.to_string().as_str(), "true")
        );
        match x.checked_add(1) {
            Some(p) => assert_eq!(vs[1], p.to_string()),
            None => assert!(vs[1].parse::<i128>().is_ok(), "{vs:?}"),
        }
        let vs = values(&exe, &["@frozen", &x.to_string()]);
        assert_eq!((vs[1].as_str(), &vs[2]), ("7", &vs[0]), "{x}");
        if let Some(f) = x.checked_add(i128::MAX) {
            assert_eq!(vs[0], f.to_string());
        }
        expect(&exe, &["@frozen_use", &x.to_string()], &["0", "7"]);
    }
}
