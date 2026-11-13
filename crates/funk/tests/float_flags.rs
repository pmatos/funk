//! The fast-math flags build and run natively at `f32` and `f64` (#242,
//! `docs/decisions/x86-64-backend-lowering-floats.md#fast-math-flags`). The
//! backend ignores `nnan`, `ninf` and `nsz`: an op without a flag refines
//! the op with it (`Fir.Core.FloatFlagLaws`), so each flagged op gives what
//! the op without flags gives, which this test checks on operands that
//! break no flag, and gives some value where the flagged op gives poison.

mod common;

use common::{build, expect, func, json_values, module, run, text};

/// `@f(%a: T, %b: T)`, which applies each float op with `flags` to `%a`
/// and `%b`, the remainders among them, and returns every result, `fcmp
/// olt` last.
fn ops(t: &str, flags: &str) -> String {
    let f = if flags.is_empty() {
        String::new()
    } else {
        format!(" {flags}")
    };
    let body = [
        format!("%s: {t} = fadd{f} round(rne) %a, %b"),
        format!("%d: {t} = fsub{f} round(rne) %a, %b"),
        format!("%m: {t} = fmul{f} round(rne) %a, %b"),
        format!("%q: {t} = fdiv{f} round(rne) %a, %b"),
        format!("%n: {t} = fneg{f} %a"),
        format!("%v: {t} = fabs{f} %n"),
        format!("%r: {t} = sqrt{f} round(rne) %b"),
        format!("%x: {t} = fma{f} round(rne) %a, %b, %a"),
        format!("%e: {t} = frem{f} %a, %b"),
        format!("%o: {t} = fmod{f} %a, %b"),
        format!("%c: i1 = fcmp{f} olt %a, %b"),
        "ret %s, %d, %m, %q, %n, %v, %r, %x, %e, %o, %c".to_string(),
    ];
    let body: Vec<&str> = body.iter().map(String::as_str).collect();
    let results = format!("{t}, {t}, {t}, {t}, {t}, {t}, {t}, {t}, {t}, {t}, i1");
    module(&[func("f", &format!("%a: {t}, %b: {t}"), &results, &body)])
}

/// The bits of `x` at `t`, as a signed integer, as the entry reads and
/// writes a float.
fn bits(t: &str, x: f64) -> String {
    if t == "f32" {
        ((x as f32).to_bits() as i32).to_string()
    } else {
        (x.to_bits() as i64).to_string()
    }
}

/// What `@f` gives on `a` and `b` without flags, by the host's arithmetic.
fn want(t: &str, a: f64, b: f64) -> Vec<String> {
    let r = |x: f64| bits(t, x);
    let fma = if t == "f32" {
        f64::from((a as f32).mul_add(b as f32, a as f32))
    } else {
        a.mul_add(b, a)
    };
    // IEEE 754's remainder and C's `fmod`, exact on these operands.
    let frem = a - (a / b).round_ties_even() * b;
    let mut v: Vec<String> = [
        a + b,
        a - b,
        a * b,
        a / b,
        -a,
        a.abs(),
        b.sqrt(),
        fma,
        frem,
        a % b,
    ]
    .into_iter()
    .map(r)
    .collect();
    v.push((a < b).to_string());
    v
}

#[test]
fn flagged_ops_give_the_results_of_ops_without_flags() {
    for t in ["f32", "f64"] {
        for flags in ["", "nnan", "ninf", "nsz", "nnan ninf nsz"] {
            let name = format!("flags-{t}-{}", flags.replace(' ', "-"));
            let exe = build(&name, &ops(t, flags));
            for (a, b) in [(1.5, 2.0), (-3.25, 0.5), (6.0, 4.0)] {
                let want = want(t, a, b);
                let want: Vec<&str> = want.iter().map(String::as_str).collect();
                expect(&exe, &["@f", &bits(t, a), &bits(t, b)], &want);
            }
        }
    }
}

/// Where a flag makes the result poison, native code gives some value,
/// which refines it: the run ends normally, with a value for each result
/// and nothing on stderr.
#[test]
fn flagged_ops_run_where_their_result_is_poison() {
    for t in ["f32", "f64"] {
        let exe = build(&format!("flags-poison-{t}"), &ops(t, "nnan ninf"));
        for (a, b) in [(f64::NAN, 1.0), (f64::INFINITY, 2.0), (0.0, 0.0)] {
            let out = run(&exe, &["@f", &bits(t, a), &bits(t, b)]);
            assert!(out.status.success(), "{t} {a} {b}: {out:?}");
            assert!(out.stderr.is_empty(), "{t} {a} {b}: {out:?}");
            assert_eq!(json_values(&text(&out.stdout)).len(), 11, "{t} {a} {b}");
        }
    }
}
