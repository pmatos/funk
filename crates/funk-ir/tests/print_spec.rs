//! The printer writes the bytes that the spec's own checks fix
//! (`#guard`s in `lean/Fir/Text/Example.lean`). Printing needs no registry,
//! so these modules use ops that the tracer does not register yet.

use funk_ir::dialects::core::int_type;
use funk_ir::text::{print_func, print_op};
use funk_ir::{Attr, Block, Func, LocRef, LocTable, Location, Module, Op, Region, print};

fn range(file: &str, l1: u32, c1: u32, l2: u32, c2: u32) -> Location {
    Location::Range {
        file: file.into(),
        start_line: l1,
        start_col: c1,
        end_line: l2,
        end_col: c2,
    }
}

fn sum_module() -> Module {
    let i32 = int_type(32);
    let i1 = int_type(1);
    let l = LocRef;
    let sum = Func::new("sum")
        .param("n", i32.clone())
        .result(i32.clone())
        .block(
            Block::new("entry")
                .op(Op::new("const", l(1))
                    .attr(Attr::int(0))
                    .result("zero", i32.clone()))
                .op(Op::new("br", l(1)).succ("loop", &["zero", "zero"])),
        )
        .block(
            Block::new("loop")
                .param("i", i32.clone())
                .param("acc", i32.clone())
                .op(Op::new("icmp", l(2))
                    .attr(Attr::word("sge"))
                    .operand("i")
                    .operand("n")
                    .result("done", i1))
                .op(Op::new("cond_br", l(2))
                    .operand("done")
                    .succ("exit", &["acc"])
                    .succ("body", &[])),
        )
        .block(
            Block::new("body")
                .op(Op::new("add", l(3))
                    .attr(Attr::word("nsw"))
                    .operand("acc")
                    .operand("i")
                    .result("acc1", i32.clone()))
                .op(Op::new("const", l(3))
                    .attr(Attr::int(1))
                    .result("one", i32.clone()))
                .op(Op::new("add", l(3))
                    .attr(Attr::word("nsw"))
                    .operand("i")
                    .operand("one")
                    .result("i1", i32.clone()))
                .op(Op::new("br", l(3)).succ("loop", &["i1", "acc1"])),
        )
        .block(
            Block::new("exit")
                .param("r", i32.clone())
                .op(Op::new("ret", l(4)).operand("r")),
        );
    let sum10 = Func::new("sum10").result(i32.clone()).block(
        Block::new("entry")
            .op(Op::new("const", l(5))
                .attr(Attr::int(10))
                .result("ten", i32.clone()))
            .op(Op::new("call", l(6))
                .attr(Attr::Sym("sum".into()))
                .operand("ten")
                .result("s", i32))
            .op(Op::new("ret", l(0)).operand("s")),
    );
    let mut locs = LocTable::new();
    locs.push(Location::Unknown);
    locs.push(range("sum.c", 2, 3, 2, 15));
    locs.push(range("sum.c", 3, 10, 3, 16));
    locs.push(range("sum.c", 4, 5, 4, 17));
    locs.push(range("sum.c", 6, 3, 6, 14));
    locs.push(range("main.c", 2, 19, 2, 21));
    locs.push(range("main.c", 2, 15, 2, 22));
    Module {
        locs,
        ..Module::new()
    }
    .func(sum)
    .func(sum10)
}

#[test]
fn the_sum_example_prints_as_the_spec_says() {
    let expected = [
        "func @sum(%n: i32) -> i32 {",
        "^entry:",
        "  %zero: i32 = const 0 @1",
        "  br ^loop(%zero, %zero) @1",
        "^loop(%i: i32, %acc: i32):",
        "  %done: i1 = icmp sge %i, %n @2",
        "  cond_br %done, ^exit(%acc), ^body @2",
        "^body:",
        "  %acc1: i32 = add nsw %acc, %i @3",
        "  %one: i32 = const 1 @3",
        "  %i1: i32 = add nsw %i, %one @3",
        "  br ^loop(%i1, %acc1) @3",
        "^exit(%r: i32):",
        "  ret %r @4",
        "}",
        "",
        "func @sum10() -> i32 {",
        "^entry:",
        "  %ten: i32 = const 10 @5",
        "  %s: i32 = call @sum %ten @6",
        "  ret %s @0",
        "}",
        "",
        "locs {",
        "  @0 = unknown",
        "  @1 = \"sum.c\":2:3 to 2:15",
        "  @2 = \"sum.c\":3:10 to 3:16",
        "  @3 = \"sum.c\":4:5 to 4:17",
        "  @4 = \"sum.c\":6:3 to 6:14",
        "  @5 = \"main.c\":2:19 to 2:21",
        "  @6 = \"main.c\":2:15 to 2:22",
        "}",
        "",
    ]
    .join("\n");
    assert_eq!(print(&sum_module()), expected);
}

#[test]
fn a_region_prints_two_spaces_deeper_than_its_op() {
    let inner = Region::new(vec![Block::new("inner").op(Op::new("ret", LocRef(0)))]);
    let op = Op::new("br", LocRef(7)).region(inner);
    assert_eq!(
        print_op(&op, 2),
        "  br {\n    ^inner:\n      ret @0\n  } @7\n"
    );
}

#[test]
fn symbols_that_are_not_words_are_quoted() {
    let f = Func::new("1").block(
        Block::new("entry")
            .op(Op::new("call", LocRef(0)).attr(Attr::Sym("a b".into())))
            .op(Op::new("ret", LocRef(0))),
    );
    assert_eq!(
        print_func(&f),
        "func @\"1\"() {\n^entry:\n  call @\"a b\" @0\n  ret @0\n}\n"
    );
}

#[test]
fn an_applied_word_with_no_arguments_is_not_the_word() {
    assert_eq!(Attr::App("h".into(), vec![]).to_string(), "h()");
    assert_eq!(Attr::word("h").to_string(), "h");
}

#[test]
fn every_text_ends_with_a_line_feed() {
    assert_eq!(print(&Module::new()), "locs {\n}\n");
    assert!(print(&sum_module()).ends_with('\n'));
}
