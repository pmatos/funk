//! `i128` across calls and branches (#21), run natively and checked against
//! Rust's `i128` arithmetic. An `i128` argument takes two registers when
//! two are left, and otherwise 16 bytes of the stack, aligned to 16, while a
//! later narrower argument still takes a register that it left; an `i128`
//! result comes back in `%rdx:%rax` (ADR-2026-11-03-0108). Block arguments
//! move both halves of an `i128` in one parallel move
//! (ADR-2026-11-03-010730).

mod common;

use common::{boundaries, build, expect, module, spell, wrap};

/// Values of `i128` on both sides of the 64-bit boundary.
const WIDE: [i128; 8] = [
    i128::MIN,
    -(1 << 64),
    -1,
    0,
    1,
    (1 << 64) - 1,
    0x0123_4567_89ab_cdef_fedc_ba98_7654_3210,
    i128::MAX,
];

/// The text of `func @name(params) -> result` with the lines `lines`: an
/// op at `@0`, or a block's label, which starts with `^`.
fn func(name: &str, params: &str, result: &str, lines: &[String]) -> String {
    let mut text = format!("func @{name}({params}) -> {result} {{\n^entry:\n");
    for l in lines {
        if l.starts_with('^') {
            text.push_str(&format!("{l}\n"));
        } else {
            text.push_str(&format!("  {l} @0\n"));
        }
    }
    text + "}\n"
}

fn lines(ls: &[&str]) -> Vec<String> {
    ls.iter().map(|l| l.to_string()).collect()
}

/// What the callee folds its arguments with: multiply, then add the next.
const K: i128 = 1_000_003;

/// Parameter lists that put `i128`s in registers, on the stack, after a
/// hole, and before a narrower argument that takes the register they left.
const LISTS: [&[u32]; 8] = [
    &[128, 128, 128],
    &[128, 128, 128, 128],
    &[64, 64, 64, 64, 64, 128, 64],
    &[64, 64, 64, 64, 64, 64, 64, 128, 64],
    &[64, 128, 128, 128],
    &[128, 64, 128, 64, 128, 64, 128, 8, 128],
    &[1, 128, 16, 128, 32, 128, 64, 128],
    &[128, 128, 128, 1, 128, 8, 8, 128],
];

/// `@calleeN`, which folds its parameters, of the widths `ws` reversed,
/// and `@callN`, which adds one to each of its parameters, of the widths
/// `ws`, and passes them to it in reverse order. So the two lay out
/// different lists, and an argument in the wrong place, or read from the
/// wrong half, changes the result.
fn pair(n: usize, ws: &[u32]) -> [String; 2] {
    let rev: Vec<u32> = ws.iter().rev().copied().collect();
    let params = |ws: &[u32]| -> String {
        let ps: Vec<String> = ws
            .iter()
            .enumerate()
            .map(|(k, w)| format!("%p{k}: i{w}"))
            .collect();
        ps.join(", ")
    };
    let mut callee = vec![
        "%acc0: i128 = const 0".to_string(),
        format!("%k: i128 = const {K}"),
    ];
    for (k, w) in rev.iter().enumerate() {
        let x = if *w == 128 {
            format!("%p{k}")
        } else {
            callee.push(format!("%x{k}: i128 = sext %p{k}"));
            format!("%x{k}")
        };
        callee.push(format!("%m{k}: i128 = mul %acc{k}, %k"));
        callee.push(format!("%acc{}: i128 = add %m{k}, {x}", k + 1));
    }
    callee.push(format!("ret %acc{}", rev.len()));
    let mut caller = Vec::new();
    for (k, w) in ws.iter().enumerate() {
        let one = if *w == 1 { "true" } else { "1" };
        caller.push(format!("%one{k}: i{w} = const {one}"));
        caller.push(format!("%q{k}: i{w} = add %p{k}, %one{k}"));
    }
    let args: Vec<String> = (0..ws.len()).rev().map(|k| format!("%q{k}")).collect();
    caller.push(format!("%r: i128 = call @callee{n} {}", args.join(", ")));
    caller.push("ret %r".into());
    [
        func(&format!("callee{n}"), &params(&rev), "i128", &callee),
        func(&format!("call{n}"), &params(ws), "i128", &caller),
    ]
}

/// The value of `iW` that parameter `k` takes in run `r`: each width runs
/// through its boundary values, and `i128` through [`WIDE`].
fn value(w: u32, k: usize, r: usize) -> i128 {
    if w == 128 {
        WIDE[(k * 3 + r) % WIDE.len()]
    } else {
        let b = boundaries(w);
        b[(k + r) % b.len()]
    }
}

#[test]
fn i128_arguments_pass_in_registers_and_on_the_stack_in_every_layout() {
    let funcs: Vec<String> = LISTS
        .iter()
        .enumerate()
        .flat_map(|(n, ws)| pair(n, ws))
        .collect();
    let exe = build("i128-call-layouts", &module(&funcs));
    for (n, ws) in LISTS.iter().enumerate() {
        for r in 0..WIDE.len() {
            let vs: Vec<i128> = ws
                .iter()
                .enumerate()
                .map(|(k, &w)| value(w, k, r))
                .collect();
            let plus: Vec<i128> = ws
                .iter()
                .zip(&vs)
                .map(|(&w, &v)| {
                    if w == 128 {
                        v.wrapping_add(1)
                    } else {
                        wrap(w, v + 1)
                    }
                })
                .collect();
            let want = plus
                .iter()
                .rev()
                .fold(0i128, |acc, &x| acc.wrapping_mul(K).wrapping_add(x));
            let name = format!("@call{n}");
            let spelled: Vec<String> = ws.iter().zip(&vs).map(|(&w, &v)| spell(w, v)).collect();
            let mut args = vec![name.as_str()];
            args.extend(spelled.iter().map(String::as_str));
            expect(&exe, &args, &[&want.to_string()]);
        }
    }
}

/// `n!` and the `n`-th Fibonacci number at `i128`, wrapped: `34!` is past
/// `2^127`, and each call returns its result in `%rdx:%rax`.
#[test]
fn recursion_returns_i128_results() {
    let fact = "func @fact(%n: i128) -> i128 {\n^entry:\n  %zero: i128 = const 0 @0\n  %one: i128 = const 1 @0\n  %done: i1 = icmp sle %n, %zero @0\n  cond_br %done, ^base, ^step @0\n^base:\n  ret %one @0\n^step:\n  %m: i128 = sub %n, %one @0\n  %f: i128 = call @fact %m @0\n  %r: i128 = mul %n, %f @0\n  ret %r @0\n}\n";
    let fib = "func @fib(%n: i128, %big: i128) -> i128 {\n^entry:\n  %one: i128 = const 1 @0\n  %two: i128 = const 2 @0\n  %small: i1 = icmp slt %n, %two @0\n  cond_br %small, ^base, ^step @0\n^base:\n  %b: i128 = mul %n, %big @0\n  ret %b @0\n^step:\n  %m: i128 = sub %n, %one @0\n  %l: i128 = sub %n, %two @0\n  %a: i128 = call @fib %m, %big @0\n  %c: i128 = call @fib %l, %big @0\n  %r: i128 = add %a, %c @0\n  ret %r @0\n}\n";
    let exe = build(
        "i128-recursion",
        &format!("{fact}\n{fib}\nlocs {{\n  @0 = unknown\n}}\n"),
    );
    let mut f = 1i128;
    for n in 0..=40 {
        if n > 0 {
            f = f.wrapping_mul(n);
        }
        expect(&exe, &["@fact", &n.to_string()], &[&f.to_string()]);
    }
    let fibs = |n: usize| {
        let mut v = vec![0i128, 1];
        for k in 2..=n {
            v.push(v[k - 1] + v[k - 2]);
        }
        v[n]
    };
    for n in [0, 1, 2, 10, 20] {
        for big in [1, (1 << 64) + 3, i128::MAX] {
            let want = fibs(n).wrapping_mul(big);
            let args = ["@fib", &n.to_string(), &big.to_string()];
            expect(&exe, &args, &[&want.to_string()]);
        }
    }
}

/// Block arguments at `i128`: a swap and a rotation of three round a loop,
/// next to an `i8` argument that counts down, and a loop that sums.
#[test]
fn block_arguments_move_both_halves_round_loops() {
    let swap = func(
        "swap",
        "%a: i128, %b: i128, %n: i8",
        "i128",
        &lines(&[
            "%zero: i8 = const 0",
            "%one: i8 = const 1",
            "br ^loop(%a, %b, %n)",
            "^loop(%x: i128, %y: i128, %i: i8):",
            "%more: i1 = icmp ne %i, %zero",
            "%j: i8 = sub %i, %one",
            "cond_br %more, ^loop(%y, %x, %j), ^done",
            "^done:",
            "ret %x",
        ]),
    );
    let rotate = func(
        "rotate",
        "%a: i128, %b: i128, %c: i128, %n: i8",
        "i128",
        &lines(&[
            "%zero: i8 = const 0",
            "%one: i8 = const 1",
            "br ^loop(%n, %a, %b, %c)",
            "^loop(%i: i8, %x: i128, %y: i128, %z: i128):",
            "%more: i1 = icmp ne %i, %zero",
            "%j: i8 = sub %i, %one",
            "cond_br %more, ^loop(%j, %y, %z, %x), ^done",
            "^done:",
            "%k: i128 = const 1000003",
            "%xk: i128 = mul %x, %k",
            "%s: i128 = add %xk, %y",
            "%sk: i128 = mul %s, %k",
            "%t: i128 = add %sk, %z",
            "ret %t",
        ]),
    );
    let sum = func(
        "sum",
        "%step: i128, %n: i8",
        "i128",
        &lines(&[
            "%zero: i8 = const 0",
            "%one: i8 = const 1",
            "%acc0: i128 = const 0",
            "br ^loop(%acc0, %step, %n)",
            "^loop(%acc: i128, %v: i128, %i: i8):",
            "%more: i1 = icmp ne %i, %zero",
            "%next: i128 = add %acc, %v",
            "%j: i8 = sub %i, %one",
            "cond_br %more, ^loop(%next, %v, %j), ^done",
            "^done:",
            "ret %acc",
        ]),
    );
    let exe = build("i128-blocks", &module(&[swap, rotate, sum]));
    for (k, &a) in WIDE.iter().enumerate() {
        let b = WIDE[(k + 3) % WIDE.len()];
        let c = WIDE[(k + 5) % WIDE.len()];
        let (sa, sb, sc) = (a.to_string(), b.to_string(), c.to_string());
        for n in [0i8, 1, 2, 3, 7] {
            let sn = n.to_string();
            let x = if n % 2 == 0 { a } else { b };
            expect(&exe, &["@swap", &sa, &sb, &sn], &[&x.to_string()]);
            let mut t = [a, b, c];
            t.rotate_left(n as usize % 3);
            let want = t[0]
                .wrapping_mul(K)
                .wrapping_add(t[1])
                .wrapping_mul(K)
                .wrapping_add(t[2]);
            expect(&exe, &["@rotate", &sa, &sb, &sc, &sn], &[&want.to_string()]);
            let want = a.wrapping_mul(i128::from(n));
            expect(&exe, &["@sum", &sa, &sn], &[&want.to_string()]);
        }
    }
}
