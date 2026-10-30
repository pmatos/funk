//! A test-only dialect, registered from outside `funk-ir`, shows that a new
//! dialect needs no change to the IR, the parser or the printer (G0).
//!
//! Its ops are named `toy.` and a word, so they cannot collide with a core
//! op: `.` is reserved for a dialect's name before its ops (H4), and no core
//! op name contains one. That is the rule for test dialects
//! (ADR-2026-10-30-1146), not a decision on H4.

mod common;

use funk_ir::dialects::core::{core_type, int_type, int_width};
use funk_ir::{
    Attr, Dialect, OpContext, OpShape, OpSpec, OpTypes, Registry, Type, TypeCheck, TypeSpec, parse,
    print, verify,
};

/// An op of the toy dialect, with its decoding as a function.
struct ToyOp(&'static str, fn(&OpTypes<'_>) -> Result<OpShape, String>);

impl OpSpec for ToyOp {
    fn name(&self) -> &str {
        self.0
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        (self.1)(op)
    }

    fn check(&self, cx: &OpContext<'_>, _op: &OpTypes<'_>) -> Result<(), String> {
        if self.0 == "toy.make" && cx.func == "forbidden" {
            return Err("toy.make is not allowed in @forbidden".into());
        }
        Ok(())
    }
}

/// `toy.tok`, and `toy.vec(N)` for a positive `N`.
struct ToyTypes;

impl TypeSpec for ToyTypes {
    fn check(&self, ty: &Type) -> Option<TypeCheck> {
        match (ty.name.as_str(), ty.args.as_deref()) {
            ("toy.tok", None) => Some(TypeCheck::Valid),
            ("toy.vec", Some([Attr::Int(n)])) if n.as_str() == "0" => Some(TypeCheck::Invalid(
                "a toy.vec holds at least one element".into(),
            )),
            ("toy.vec", Some([Attr::Int(n)])) if !n.is_negative() => Some(TypeCheck::Valid),
            ("toy.vec", _) => Some(TypeCheck::Malformed("toy.vec takes one size".into())),
            _ => None,
        }
    }
}

fn is(ty: &Type, name: &str) -> bool {
    ty.name == name
}

fn plain(ok: bool, shape: OpShape) -> Result<OpShape, String> {
    if ok {
        Ok(shape)
    } else {
        Err("toy op used at the wrong types".into())
    }
}

fn term(successors: usize) -> OpShape {
    OpShape {
        terminator: true,
        successors,
        symbols: vec![],
    }
}

fn toy() -> Dialect {
    Dialect::new("toy")
        .types(ToyTypes)
        .op(ToyOp("toy.make", |o| {
            plain(
                o.operands.is_empty() && matches!(o.results, [t] if is(t, "toy.tok")),
                OpShape::default(),
            )
        }))
        .op(ToyOp("toy.use", |o| {
            let ok = matches!(o.operands, [t] if is(t, "toy.tok"))
                && matches!(o.results, [r] if int_width(r).is_some());
            plain(ok, OpShape::default())
        }))
        .op(ToyOp("toy.mix", |o| {
            let ok = o.attrs.len() == 1
                && o.operands
                    .iter()
                    .chain(o.results)
                    .all(|t| core_type(t).is_some());
            plain(ok, OpShape::default())
        }))
        .op(ToyOp("toy.br", |o| {
            plain(o.operands.is_empty() && o.results.is_empty(), term(1))
        }))
        .op(ToyOp("toy.cond", |o| {
            plain(o.operands == [int_type(1)] && o.results.is_empty(), term(2))
        }))
        .op(ToyOp("toy.ref", |o| match o.attrs {
            [Attr::Sym(s)] => Ok(OpShape {
                symbols: vec![s.clone()],
                ..OpShape::default()
            }),
            _ => Err("toy.ref refers to one symbol".into()),
        }))
        .op(ToyOp("toy.scope", |o| {
            plain(
                o.operands.is_empty() && o.results.is_empty(),
                OpShape::default(),
            )
        }))
}

fn registry() -> Registry {
    let mut r = Registry::core();
    r.register(toy()).expect("the toy dialect registers");
    r
}

const TOY_MODULE: &str = "\
func @g(%n: i32, %c: i1) -> i32 {
^entry:
  %t: toy.tok = toy.make @1
  %x: i32 = toy.use %t @2
  %m: i32 = toy.mix pair(1, -2, \"s\", @\"1\", w(), x) %x, %n @2
  toy.ref @g @0
  toy.ref @\"1\" @0
  toy.cond %c, ^left(%m), ^right @3
^left(%l: i32):
  toy.br ^join(%l) @3
^right:
  toy.br ^join(%n) @3
^join(%j: i32):
  %v: toy.vec(4) = toy.make2 @0
  ret %j @4
}

func @\"1\"() {
^entry:
  ret @0
}

locs {
  @0 = unknown
  @1 = \"toy.c\":1:1 to 1:9
  @2 = name(\"x\")
  @3 = derived(@1)
  @4 = fused(@1, @2)
}
";

/// The toy module without the line that no dialect decodes.
fn toy_module() -> String {
    TOY_MODULE.replace("  %v: toy.vec(4) = toy.make2 @0\n", "")
}

#[test]
fn a_module_of_toy_ops_parses_verifies_prints_and_round_trips() {
    let reg = registry();
    let text = toy_module();
    let m = parse(&text, &reg).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(verify(&m, &reg), vec![]);
    assert_eq!(print(&m), text);
    assert_eq!(parse(&print(&m), &reg), Ok(m));
    assert_eq!(reg.dialect_of("toy.mix"), Some("toy"));
    assert_eq!(reg.dialect_of("add"), Some("core"));
}

#[test]
fn an_op_or_type_that_no_dialect_decodes_is_a_parse_error() {
    let e = parse(TOY_MODULE, &registry()).unwrap_err();
    assert!(e.reason.contains("unknown op toy.make2"), "{e}");
    let e = parse(&toy_module(), &Registry::core()).unwrap_err();
    assert!(e.reason.contains("toy.tok is not a type"), "{e}");
    let wrong = toy_module().replace("toy.use %t", "toy.use %n");
    assert!(
        parse(&wrong, &registry())
            .unwrap_err()
            .reason
            .contains("toy op used at the wrong types")
    );
    let bad_ty = toy_module().replace("%c: i1)", "%c: i1, %v: toy.vec())");
    assert!(
        parse(&bad_ty, &registry())
            .unwrap_err()
            .reason
            .contains("toy.vec takes one size")
    );
}

/// A function `@f(%n: i32, %c: i1) -> i32` with this body.
fn branches(body: &str) -> String {
    format!("func @f(%n: i32, %c: i1) -> i32 {{\n{body}}}\n\nlocs {{\n  @0 = unknown\n}}\n")
}

fn diags(text: &str) -> Vec<String> {
    let reg = registry();
    let m = parse(text, &reg).unwrap_or_else(|e| panic!("{e}\n{text}"));
    verify(&m, &reg)
        .into_iter()
        .map(|d| d.to_string())
        .collect()
}

#[test]
fn branches_with_block_arguments_are_valid() {
    let text = branches(
        "^entry:\n  toy.cond %c, ^left(%n), ^right @0\n^left(%l: i32):\n  toy.br ^join(%l) @0\n^right:\n  toy.br ^join(%n) @0\n^join(%j: i32):\n  ret %j @0\n",
    );
    assert_eq!(diags(&text), Vec::<String>::new());
    let looped = "^entry:\n  toy.br ^loop(%n) @0\n^loop(%i: i32):\n  %k: i32 = add %i, %n @0\n  toy.cond %c, ^loop(%k), ^exit @0\n^exit:\n  ret %n @0\n";
    assert_eq!(diags(&branches(looped)), Vec::<String>::new());
}

#[test]
fn a_definition_must_dominate_its_uses_across_blocks() {
    let text = branches(
        "^entry:\n  toy.cond %c, ^left, ^right @0\n^left:\n  %x: i32 = add %n, %n @0\n  toy.br ^join @0\n^right:\n  toy.br ^join @0\n^join:\n  ret %x @0\n",
    );
    let ds = diags(&text);
    assert!(
        ds.iter()
            .any(|d| d.contains("%x is defined in ^left, which does not dominate ^join")),
        "{ds:#?}"
    );
    let arg = branches(
        "^entry:\n  toy.cond %c, ^left(%n), ^right @0\n^left(%l: i32):\n  toy.br ^right @0\n^right:\n  ret %l @0\n",
    );
    let ds = diags(&arg);
    assert!(
        ds.iter()
            .any(|d| d.contains("%l is an argument of ^left, which does not dominate ^right")),
        "{ds:#?}"
    );
}

#[test]
fn a_block_that_branches_cannot_reach_is_rejected() {
    let text = branches("^entry:\n  toy.br ^b @0\n^b:\n  ret %n @0\n^island:\n  toy.br ^b @0\n");
    let ds = diags(&text);
    assert_eq!(ds.len(), 1, "{ds:#?}");
    assert!(ds[0].contains("block ^island is not reachable from the entry"));
}

#[test]
fn successors_are_checked_against_the_registration() {
    let ds = diags(&branches(
        "^entry:\n  toy.br ^a, ^b @0\n^a:\n  ret %n @0\n^b:\n  ret %n @0\n",
    ));
    assert!(
        ds.iter()
            .any(|d| d.contains("toy.br has 2 successors, and its registration says 1")),
        "{ds:#?}"
    );
    let ds = diags(&branches("^entry:\n  toy.br ^b(%n) @0\n^b:\n  ret %n @0\n"));
    assert!(
        ds.iter()
            .any(|d| d.contains("passes (i32) but the block takes ()")),
        "{ds:#?}"
    );
}

#[test]
fn a_symbol_that_an_op_refers_to_must_name_a_function() {
    let ds = diags(&branches("^entry:\n  toy.ref @missing @0\n  ret %n @0\n"));
    assert!(
        ds.iter()
            .any(|d| d.contains("toy.ref refers to @missing, which names no function")),
        "{ds:#?}"
    );
    assert_eq!(
        diags(&branches("^entry:\n  toy.ref @f @0\n  ret %n @0\n")),
        Vec::<String>::new()
    );
}

#[test]
fn a_dialect_rule_can_read_the_op_context() {
    let text = "func @forbidden() {\n^entry:\n  %t: toy.tok = toy.make @0\n  ret @0\n}\n\nlocs {\n  @0 = unknown\n}\n";
    assert!(
        diags(text)
            .iter()
            .any(|d| d.contains("toy.make is not allowed in @forbidden"))
    );
}

#[test]
fn regions_round_trip_and_validation_rejects_them() {
    let text = branches(
        "^entry:\n  toy.scope {\n    ^inner(%k: i32):\n      toy.scope {\n      } {\n        ^deeper:\n          ret %k @0\n      } @0\n  } @0\n  ret %n @0\n",
    );
    let reg = registry();
    let m = parse(&text, &reg).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(print(&m), text);
    assert!(
        diags(&text)
            .iter()
            .any(|d| d.contains("op toy.scope owns a region"))
    );
}

#[test]
fn types_are_extensible_and_checked() {
    let text = "func @f(%v: toy.vec(0)) {\n^entry:\n  ret @0\n}\n\nlocs {\n  @0 = unknown\n}\n";
    assert!(
        diags(text)
            .iter()
            .any(|d| d.contains("a toy.vec holds at least one element"))
    );
    let ok = text.replace("toy.vec(0)", "toy.vec(3)");
    assert_eq!(diags(&ok), Vec::<String>::new());
}

#[test]
fn registration_rejects_names_that_collide_or_cannot_be_written() {
    struct Named(&'static str);
    impl OpSpec for Named {
        fn name(&self) -> &str {
            self.0
        }
        fn decode(&self, _: &OpTypes<'_>) -> Result<OpShape, String> {
            Ok(OpShape::default())
        }
    }
    let mut r = Registry::core();
    assert!(r.register(Dialect::new("dup").op(Named("add"))).is_err());
    assert!(r.register(Dialect::new("bad").op(Named("toy op"))).is_err());
    assert!(
        r.register(Dialect::new("twice").op(Named("toy.a")).op(Named("toy.a")))
            .is_err()
    );
    assert!(r.register(Dialect::new("core")).is_err());
    assert!(
        r.op("toy.a").is_none(),
        "a failed registration changes nothing"
    );
    assert!(r.register(Dialect::new("fine").op(Named("toy.a"))).is_ok());
}
