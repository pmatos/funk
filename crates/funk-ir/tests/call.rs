//! `call` (#20): a call by symbol to any function of the module, the caller
//! itself and mutual recursion included, with any number of arguments and
//! results, none included (ADR-2026-10-29-2008). It goes through the core
//! dialect's registry: the parser, the printer, the builder and the
//! verifier have no code of their own for it (ADR-2026-10-30-1146).

mod common;

use std::collections::HashSet;

use common::{one_func, parse_ok};
use funk_ir::dialects::core::int_type;
use funk_ir::generate::{self, Rng};
use funk_ir::{Attr, Block, Func, Location, Module, Op, Registry, print, verify};

/// Asserts that `text` parses, is valid and prints as itself.
fn valid(text: &str) -> Module {
    let m = parse_ok(text);
    assert_eq!(verify(&m, &Registry::core()), vec![], "\n{text}");
    assert_eq!(print(&m), text);
    m
}

/// Recursive factorial at `iW`, and `@twice`, which calls it twice.
fn fact_text(w: u32) -> String {
    let one = if w == 1 { "true" } else { "1" };
    let zero = if w == 1 { "false" } else { "0" };
    one_func(&format!(
        "func @fact(%n: i{w}) -> i{w} {{
^entry:
  %zero: i{w} = const {zero} @0
  %more: i1 = icmp sgt %n, %zero @0
  cond_br %more, ^rec, ^base @0
^rec:
  %one: i{w} = const {one} @0
  %m: i{w} = sub %n, %one @0
  %f: i{w} = call @fact %m @0
  %p: i{w} = mul %n, %f @0
  ret %p @0
^base:
  %b: i{w} = const {one} @0
  ret %b @0
}}

func @twice(%n: i{w}) -> i{w} {{
^entry:
  %a: i{w} = call @fact %n @0
  %b: i{w} = call @fact %a @0
  ret %b @0
}}
"
    ))
}

/// The same module as [`fact_text`], built with the builder.
fn fact_built(w: u32) -> Module {
    let t = int_type(w);
    let (one, zero) = if w == 1 {
        (Attr::word("true"), Attr::word("false"))
    } else {
        (Attr::int(1), Attr::int(0))
    };
    let mut m = Module::new();
    let l = m.locs.push(Location::Unknown);
    let call = |arg: &str, r: &str| {
        Op::new("call", l)
            .attr(Attr::Sym("fact".into()))
            .operand(arg)
            .result(r, t.clone())
    };
    let fact = Func::new("fact")
        .param("n", t.clone())
        .result(t.clone())
        .block(
            Block::new("entry")
                .op(Op::new("const", l).attr(zero).result("zero", t.clone()))
                .op(Op::new("icmp", l)
                    .attr(Attr::word("sgt"))
                    .operand("n")
                    .operand("zero")
                    .result("more", int_type(1)))
                .op(Op::new("cond_br", l)
                    .operand("more")
                    .succ("rec", &[])
                    .succ("base", &[])),
        )
        .block(
            Block::new("rec")
                .op(Op::new("const", l)
                    .attr(one.clone())
                    .result("one", t.clone()))
                .op(Op::new("sub", l)
                    .operand("n")
                    .operand("one")
                    .result("m", t.clone()))
                .op(call("m", "f"))
                .op(Op::new("mul", l)
                    .operand("n")
                    .operand("f")
                    .result("p", t.clone()))
                .op(Op::new("ret", l).operand("p")),
        )
        .block(
            Block::new("base")
                .op(Op::new("const", l).attr(one).result("b", t.clone()))
                .op(Op::new("ret", l).operand("b")),
        );
    let twice = Func::new("twice")
        .param("n", t.clone())
        .result(t.clone())
        .block(
            Block::new("entry")
                .op(call("n", "a"))
                .op(call("a", "b"))
                .op(Op::new("ret", l).operand("b")),
        );
    m.func(fact).func(twice)
}

#[test]
fn a_function_calls_itself_at_any_width() {
    for w in [1, 7, 8, 16, 32, 33, 64, 128, 16_777_215] {
        let m = valid(&fact_text(w));
        assert_eq!(m, fact_built(w), "i{w}");
    }
}

#[test]
fn functions_call_each_other_before_and_after_their_definitions() {
    valid(&one_func(
        "func @even(%n: i8) -> i1 {
^entry:
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^yes, ^no @0
^yes:
  %t: i1 = const true @0
  ret %t @0
^no:
  %one: i8 = const 1 @0
  %m: i8 = sub %n, %one @0
  %r: i1 = call @odd %m @0
  ret %r @0
}

func @odd(%n: i8) -> i1 {
^entry:
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^yes, ^no @0
^yes:
  %f: i1 = const false @0
  ret %f @0
^no:
  %one: i8 = const 1 @0
  %m: i8 = sub %n, %one @0
  %r: i1 = call @even %m @0
  ret %r @0
}
",
    ));
}

#[test]
fn a_call_has_any_number_of_arguments_and_results() {
    valid(&one_func(
        "func @none() {
^entry:
  ret @0
}

func @swap(%a: i8, %b: i64) -> i64, i8 {
^entry:
  ret %b, %a @0
}

func @many(%a: i1, %b: i8, %c: i16, %d: i32, %e: i64, %f: i7, %g: i33, %h: i128) -> i1 {
^entry:
  ret %a @0
}

func @main(%x: i8, %y: i64) -> i8, i64, i1 {
^entry:
  call @none @0
  %p: i64, %q: i8 = call @swap %x, %y @0
  %r: i64, %s: i8 = call @swap %q, %p @0
  %t: i1 = const true @0
  %u: i16 = sext %x @0
  %v: i32 = zext %x @0
  %w: i7 = trunc %x @0
  %z: i33 = sext %x @0
  %h: i128 = zext %y @0
  %k: i1 = call @many %t, %x, %u, %v, %y, %w, %z, %h @0
  %x2: i8, %y2: i64, %k2: i1 = call @main %s, %r @0
  ret %x2, %y2, %k @0
}
",
    ));
}

#[test]
fn a_symbol_that_is_not_a_word_is_quoted() {
    valid(&one_func(
        "func @\"1\"(%x: i32) -> i32 {
^entry:
  ret %x @0
}

func @\"a b\"() {
^entry:
  ret @0
}

func @_end(%x: i32) -> i32 {
^entry:
  call @\"a b\" @0
  %y: i32 = call @\"1\" %x @0
  %z: i32 = call @_end %y @0
  ret %z @0
}
",
    ));
}

#[test]
fn the_spec_s_example_module_is_valid() {
    // `lean/Fir/Text/Example.lean`: `@sum10` calls `@sum`.
    valid(
        "func @sum(%n: i32) -> i32 {
^entry:
  %zero: i32 = const 0 @1
  br ^loop(%zero, %zero) @1
^loop(%i: i32, %acc: i32):
  %done: i1 = icmp sge %i, %n @2
  cond_br %done, ^exit(%acc), ^body @2
^body:
  %acc1: i32 = add nsw %acc, %i @3
  %one: i32 = const 1 @3
  %i1: i32 = add nsw %i, %one @3
  br ^loop(%i1, %acc1) @3
^exit(%r: i32):
  ret %r @4
}

func @sum10() -> i32 {
^entry:
  %ten: i32 = const 10 @5
  %s: i32 = call @sum %ten @6
  ret %s @0
}

locs {
  @0 = unknown
  @1 = \"sum.c\":2:3 to 2:15
  @2 = \"sum.c\":3:10 to 3:16
  @3 = \"sum.c\":4:5 to 4:17
  @4 = \"sum.c\":6:3 to 6:14
  @5 = \"main.c\":2:19 to 2:21
  @6 = \"main.c\":2:15 to 2:22
}
",
    );
}

/// The calls that the generator makes, each at least five times: a call of
/// the caller itself, of a function before it and of one after it, calls
/// with no argument, with two or more, with no result, one result and two
/// or more, a call of a function whose name the text quotes, and a module
/// in which two functions call each other.
#[test]
fn the_generator_makes_recursive_calls_with_any_number_of_results() {
    let mut seen = [0usize; 10];
    for seed in 0..generate::ROUND_TRIP_MODULES {
        let m = generate::module(&mut Rng::new(seed));
        let names: Vec<&str> = m.funcs().map(|f| f.name.as_str()).collect();
        let mut edges = HashSet::new();
        for (k, f) in m.funcs().enumerate() {
            for op in f.body.blocks.iter().flat_map(|b| &b.ops) {
                let [Attr::Sym(g)] = op.attrs.as_slice() else {
                    continue;
                };
                assert_eq!(op.name, "call");
                let at = names.iter().position(|n| n == g).expect("a function");
                edges.insert((k, at));
                seen[0] += usize::from(at == k);
                seen[1] += usize::from(at < k);
                seen[2] += usize::from(at > k);
                seen[3] += usize::from(op.operands.is_empty());
                seen[4] += usize::from(op.operands.len() >= 2);
                seen[5] += usize::from(op.results.is_empty());
                seen[6] += usize::from(op.results.len() == 1);
                seen[7] += usize::from(op.results.len() >= 2);
                seen[8] += usize::from(!funk_ir::ir::names::is_word(g));
            }
        }
        seen[9] += usize::from(
            edges
                .iter()
                .any(|&(a, b)| a != b && edges.contains(&(b, a))),
        );
    }
    assert!(seen.iter().all(|&n| n >= 5), "{seen:?}");
}
