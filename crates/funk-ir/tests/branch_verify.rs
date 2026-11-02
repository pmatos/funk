//! The rules of the control-flow graph on `br` and `cond_br` (#19):
//! `Func.Valid`, `Func.OpValid` and `Func.SuccValid` in
//! `lean/Fir/Validation/Rules.lean`, with dominance as
//! `lean/Fir/Validation/Dominance.lean` defines it. Each broken rule is a
//! validation error that names the function, the block, the op's index and
//! its location reference; a rule about a block names the block, at the
//! location of its first op.

mod common;

use common::diagnostics;
use funk_ir::{Diagnostic, LocRef};

/// A module of `@f(%n: i32, %c: i1) -> i32` with this body. Its location
/// table has `@0` to `@9`, so each op can have a reference of its own.
fn func(body: &str) -> String {
    let locs: String = (0..10).map(|k| format!("  @{k} = unknown\n")).collect();
    format!("func @f(%n: i32, %c: i1) -> i32 {{\n{body}}}\n\nlocs {{\n{locs}}}\n")
}

/// A diagnostic about the op at `index` of block `block` of `@f`, at `@loc`.
fn at_op(block: &str, index: usize, loc: u32, message: &str) -> Diagnostic {
    Diagnostic {
        message: message.into(),
        func: Some("f".into()),
        block: Some(block.into()),
        op: Some(index),
        loc: Some(LocRef(loc)),
    }
}

/// A diagnostic about block `block` of `@f`, whose first op is at `@loc`.
fn at_block(block: &str, loc: u32, message: &str) -> Diagnostic {
    Diagnostic {
        op: None,
        ..at_op(block, 0, loc, message)
    }
}

/// Asserts that `body` is rejected with exactly the diagnostics `want`.
fn rejected(body: &str, want: &[Diagnostic]) {
    let text = func(body);
    assert_eq!(diagnostics(&text), want, "\n{text}");
}

#[test]
fn a_loop_with_block_arguments_is_valid() {
    rejected(
        "^entry:
  %zero: i32 = const 0 @0
  br ^loop(%n, %zero) @1
^loop(%i: i32, %acc: i32):
  %one: i32 = const 1 @2
  %acc1: i32 = add %acc, %i @2
  %i1: i32 = sub %i, %one @2
  cond_br %c, ^loop(%i1, %acc1), ^exit(%acc1) @3
^exit(%r: i32):
  ret %r @4
",
        &[],
    );
}

#[test]
fn a_use_must_be_dominated_by_its_definition() {
    let diamond = |join: &str, right: &str| {
        format!(
            "^entry:\n  cond_br %c, ^left, ^right @0\n^left:\n  %x: i32 = const 1 @1\n  \
             br ^join(%x) @2\n^right:\n  {right} @3\n^join(%j: i32):\n  {join} @4\n"
        )
    };
    let x = "%x is defined in ^left, which does not dominate ^join";
    rejected(
        &diamond("ret %x", "br ^join(%n)"),
        &[at_op("join", 0, 4, x)],
    );
    let x = "%x is defined in ^left, which does not dominate ^right";
    rejected(
        &diamond("ret %j", "br ^join(%x)"),
        &[at_op("right", 0, 3, x)],
    );
    let arg = "%l is an argument of ^left, which does not dominate ^right";
    rejected(
        "^entry:\n  cond_br %c, ^left(%n), ^right @0\n^left(%l: i32):\n  br ^right @1\n\
         ^right:\n  ret %l @2\n",
        &[at_op("right", 0, 2, arg)],
    );
    let back = "%i1 is defined in ^body, which does not dominate ^loop";
    rejected(
        "^entry:\n  br ^loop(%n) @0\n^loop(%i: i32):\n  %k: i32 = add %i, %i1 @1\n  \
         cond_br %c, ^body, ^exit @2\n^body:\n  %i1: i32 = add %i, %n @3\n  br ^loop(%i1) @4\n\
         ^exit:\n  ret %i @5\n",
        &[at_op("loop", 0, 1, back)],
    );
    rejected(
        "^entry:\n  br ^b @0\n^b:\n  br ^c(%y) @1\n^c(%y: i32):\n  ret %y @2\n",
        &[at_op(
            "b",
            0,
            1,
            "%y is an argument of ^c, which does not dominate ^b",
        )],
    );
    let before = "%y is used before it is defined";
    rejected(
        "^entry:\n  br ^b @0\n^b:\n  %x: i32 = add %y, %n @1\n  %y: i32 = const 2 @2\n  \
         ret %x @3\n",
        &[at_op("b", 0, 1, before)],
    );
}

#[test]
fn a_successor_passes_one_value_of_the_right_type_per_argument() {
    let target = "^b(%x: i32):\n  ret %x @5\n";
    let wrong = |op: &str| format!("^entry:\n  {op} @0\n{target}");
    rejected(
        &wrong("br ^b"),
        &[at_op(
            "entry",
            0,
            0,
            "successor ^b passes () but the block takes (i32)",
        )],
    );
    rejected(
        &wrong("br ^b(%n, %n)"),
        &[at_op(
            "entry",
            0,
            0,
            "successor ^b passes (i32, i32) but the block takes (i32)",
        )],
    );
    rejected(
        &wrong("br ^b(%c)"),
        &[at_op(
            "entry",
            0,
            0,
            "successor ^b passes (i1) but the block takes (i32)",
        )],
    );
    rejected(
        &wrong("cond_br %c, ^b(%n), ^b(%c)"),
        &[at_op(
            "entry",
            0,
            0,
            "successor ^b passes (i1) but the block takes (i32)",
        )],
    );
    rejected(
        &wrong("cond_br %c, ^b, ^b(%n)"),
        &[at_op(
            "entry",
            0,
            0,
            "successor ^b passes () but the block takes (i32)",
        )],
    );
}

#[test]
fn every_block_ends_in_exactly_one_terminator() {
    rejected(
        "^entry:\n  br ^b @0\n^b:\n  %x: i32 = const 1 @1\n",
        &[at_op("b", 0, 1, "block ^b does not end with a terminator")],
    );
    rejected(
        "^entry:\n  br ^b @0\n  %x: i32 = const 1 @1\n^b:\n  ret %n @2\n",
        &[
            at_op(
                "entry",
                0,
                0,
                "br ends a block, and is not the last op of ^entry",
            ),
            at_op("entry", 1, 1, "block ^entry does not end with a terminator"),
        ],
    );
    rejected(
        "^entry:\n  cond_br %c, ^b, ^b @0\n  br ^b @1\n^b:\n  ret %n @2\n",
        &[at_op(
            "entry",
            0,
            0,
            "cond_br ends a block, and is not the last op of ^entry",
        )],
    );
}

#[test]
fn each_branch_has_as_many_successors_as_its_op() {
    let blocks = "^a:\n  br ^b @1\n^b:\n  ret %n @2\n";
    let count = |op: &str, n: usize, want: usize| {
        let name = op.split(' ').next().unwrap_or_default().to_string();
        rejected(
            &format!("^entry:\n  {op} @0\n{blocks}"),
            &[at_op(
                "entry",
                0,
                0,
                &format!("{name} has {n} successors, and its registration says {want}"),
            )],
        );
    };
    count("br ^a, ^b", 2, 1);
    count("cond_br %c, ^a", 1, 2);
    count("cond_br %c, ^a, ^b, ^a", 3, 2);
    // With no successor at all, ^a and ^b are unreachable too.
    let ds = diagnostics(&func(&format!("^entry:\n  br @0\n{blocks}")));
    let none = "br has 0 successors, and its registration says 1";
    assert!(ds.contains(&at_op("entry", 0, 0, none)), "{ds:#?}");
}

#[test]
fn a_branch_names_a_block_of_the_function() {
    let unknown = "successor ^nowhere is not a block of the function";
    rejected(
        "^entry:\n  br ^nowhere @0\n",
        &[at_op("entry", 0, 0, unknown)],
    );
    rejected(
        "^entry:\n  cond_br %c, ^b(%n), ^nowhere(%n) @0\n^b(%x: i32):\n  ret %x @1\n",
        &[at_op("entry", 0, 0, unknown)],
    );
}

#[test]
fn every_block_is_reachable_from_the_entry() {
    let not = |b: &str| format!("block ^{b} is not reachable from the entry");
    rejected(
        "^entry:\n  ret %n @0\n^dead:\n  %d: i32 = const 1 @1\n  ret %d @1\n",
        &[at_block("dead", 1, &not("dead"))],
    );
    // Blocks that branch to each other, or to themselves, but that the entry
    // does not reach, are unreachable all the same.
    rejected(
        "^entry:\n  ret %n @0\n^a:\n  br ^b @1\n^b:\n  cond_br %c, ^a, ^b @2\n^self:\n  \
         br ^self @3\n",
        &[
            at_block("a", 1, &not("a")),
            at_block("b", 2, &not("b")),
            at_block("self", 3, &not("self")),
        ],
    );
    // An unreachable block that branches into the reachable ones does not
    // make them unreachable.
    rejected(
        "^entry:\n  br ^b @0\n^b:\n  ret %n @1\n^island:\n  br ^b @2\n",
        &[at_block("island", 2, &not("island"))],
    );
}

#[test]
fn no_branch_goes_to_the_entry_block() {
    let entry = "no branch may go to the entry block ^entry";
    rejected(
        "^entry:\n  br ^b @0\n^b:\n  br ^entry @1\n",
        &[at_op("b", 0, 1, entry)],
    );
    rejected(
        "^entry:\n  cond_br %c, ^b, ^entry @0\n^b:\n  ret %n @1\n",
        &[at_op("entry", 0, 0, entry)],
    );
}

#[test]
fn a_successor_passes_only_values_the_function_defines() {
    rejected(
        "^entry:\n  br ^b(%undefined) @0\n^b(%x: i32):\n  ret %x @1\n",
        &[
            at_op(
                "entry",
                0,
                0,
                "successor argument %undefined is not defined in the function",
            ),
            at_op(
                "entry",
                0,
                0,
                "successor ^b passes (%undefined) but the block takes (i32)",
            ),
        ],
    );
    rejected(
        "^entry:\n  cond_br %c, ^b(%n), ^b(%undefined) @0\n^b(%x: i32):\n  ret %x @1\n",
        &[
            at_op(
                "entry",
                0,
                0,
                "successor argument %undefined is not defined in the function",
            ),
            at_op(
                "entry",
                0,
                0,
                "successor ^b passes (%undefined) but the block takes (i32)",
            ),
        ],
    );
}
