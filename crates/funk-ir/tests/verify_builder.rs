//! Rules that no text can break, because the parser would reject the text,
//! checked on IR built with the builder: the IR can hold what a pass makes,
//! ill-typed ops included.

use funk_ir::dialects::core::int_type;
use funk_ir::{
    Attr, Block, Diagnostic, Func, LocRef, Location, Module, Op, Region, Registry, Type, verify,
};

const L: LocRef = LocRef(0);

fn module(f: Func) -> Module {
    let mut m = Module::new();
    m.locs.push(Location::Unknown);
    m.func(f)
}

fn check(f: Func) -> Vec<Diagnostic> {
    verify(&module(f), &Registry::core())
}

fn rejects(f: Func, needle: &str) -> Vec<Diagnostic> {
    let ds = check(f);
    assert!(
        ds.iter().any(|d| d.message.contains(needle)),
        "expected {needle:?}, got {ds:#?}"
    );
    ds
}

/// `@f(%a: i32, %b: i64) -> i32` with `ops` and then `ret %a`.
fn with_ops(ops: Vec<Op>) -> Func {
    let mut b = Block::new("entry");
    for op in ops {
        b = b.op(op);
    }
    Func::new("f")
        .param("a", int_type(32))
        .param("b", int_type(64))
        .result(int_type(32))
        .block(b.op(Op::new("ret", L).operand("a")))
}

#[test]
fn a_well_built_function_is_valid() {
    let add = Op::new("add", L)
        .operand("a")
        .operand("a")
        .result("c", int_type(32));
    assert_eq!(check(with_ops(vec![add])), vec![]);
}

#[test]
fn operand_and_result_types_must_match_the_registration() {
    let mixed = Op::new("add", L)
        .operand("a")
        .operand("b")
        .result("c", int_type(32));
    let ds = rejects(
        with_ops(vec![mixed]),
        "op add does not match its registration",
    );
    assert_eq!(
        (ds[0].block.as_deref(), ds[0].op, ds[0].loc),
        (Some("entry"), Some(0), Some(L))
    );
    let result = Op::new("add", L)
        .operand("a")
        .operand("a")
        .result("c", int_type(64));
    rejects(
        with_ops(vec![result]),
        "op add does not match its registration",
    );
    let wide = Op::new("const", L)
        .attr(Attr::int(300))
        .result("c", int_type(8));
    rejects(with_ops(vec![wide]), "the constant 300 does not fit i8");
    let flagged = Op::new("add", L)
        .attr(Attr::word("nsw"))
        .operand("a")
        .operand("a")
        .result("c", int_type(32));
    rejects(with_ops(vec![flagged]), "takes no attributes");
}

#[test]
fn an_unknown_op_is_rejected() {
    let sub = Op::new("sub", L)
        .operand("a")
        .operand("a")
        .result("c", int_type(32));
    let ds = rejects(with_ops(vec![sub]), "op sub is not registered");
    assert_eq!(ds[0].loc, Some(L));
}

#[test]
fn an_operand_must_be_defined_in_the_function() {
    let undefined = Op::new("add", L)
        .operand("a")
        .operand("nope")
        .result("c", int_type(32));
    rejects(
        with_ops(vec![undefined]),
        "operand %nope is not defined in the function",
    );
    let g = Func::new("g").block(Block::new("entry").op(Op::new("ret", L).operand("a")));
    let m = module(with_ops(vec![])).func(g);
    let ds = verify(&m, &Registry::core());
    assert_eq!(ds.len(), 1, "{ds:#?}");
    assert_eq!(ds[0].func.as_deref(), Some("g"));
    assert!(ds[0].message.contains("operand %a is not defined"));
}

#[test]
fn value_names_are_unique() {
    let again = Op::new("const", L)
        .attr(Attr::int(1))
        .result("a", int_type(32));
    rejects(with_ops(vec![again]), "value %a is defined more than once");
    let twice = Func::new("f")
        .param("x", int_type(8))
        .param("x", int_type(8))
        .block(Block::new("e").op(Op::new("ret", L)));
    rejects(twice, "value %x is defined more than once");
}

#[test]
fn names_and_labels_are_name_characters() {
    let spaced = Op::new("const", L)
        .attr(Attr::int(1))
        .result("c d", int_type(32));
    rejects(
        with_ops(vec![spaced]),
        "value name \"c d\" is not one or more name characters",
    );
    let empty = Op::new("const", L)
        .attr(Attr::int(1))
        .result("", int_type(32));
    rejects(with_ops(vec![empty]), "value name \"\"");
    let f = Func::new("f").block(Block::new("a-b").op(Op::new("ret", L)));
    rejects(f, "label \"a-b\" is not one or more name characters");
    let inner = Region::new(vec![
        Block::new("in ner")
            .param("x y", int_type(8))
            .op(Op::new("ret", L)),
    ]);
    let f = Func::new("f").block(Block::new("entry").op(Op::new("ret", L).region(inner)));
    let ds = rejects(f, "label \"in ner\"");
    assert!(ds.iter().any(|d| d.message.contains("value name \"x y\"")));
}

#[test]
fn every_type_decodes_and_is_valid() {
    let f = Func::new("f")
        .param("x", Type::word("u8"))
        .block(Block::new("e").op(Op::new("ret", L)));
    rejects(f, "the type of %x, u8, does not decode");
    let f = Func::new("f")
        .result(Type::word("i032"))
        .block(Block::new("e").op(Op::new("ret", L)));
    rejects(
        f,
        "a result type of the function, i032, does not decode: the width of i032 has a leading zero",
    );
    let f = Func::new("f")
        .param("x", Type::word("u8"))
        .result(Type::word("u8"));
    let f = f.block(Block::new("e").op(Op::new("ret", L).operand("x")));
    rejects(f, "ret returns values of core types, not u8");
}

#[test]
fn ops_with_successors_need_their_registration() {
    let br = Op::new("ret", L).operand("a").succ("b", &[]);
    let f = with_ops(vec![]).block(Block::new("b").op(Op::new("ret", L).operand("a")));
    let mut f = f;
    f.body.blocks[0].ops[0] = br;
    rejects(f, "ret has 1 successors, and its registration says 0");
}

/// No op exists without a location: `Op::new` takes one, and the field is
/// not optional. `unknown` is an entry of the table like any other.
#[test]
fn every_op_has_a_location() {
    let op = Op::new("ret", LocRef(3));
    assert_eq!(op.loc, LocRef(3));
    let mut m = module(Func::new("f").block(Block::new("e").op(op)));
    assert!(
        verify(&m, &Registry::core())
            .iter()
            .any(|d| d.message.contains("@3 is not in the location table"))
    );
    m.locs.insert(LocRef(3), Location::Unknown);
    assert_eq!(verify(&m, &Registry::core()), vec![]);
}
