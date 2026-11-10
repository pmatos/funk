//! A module's dialect set (ADR-2026-11-10-1306), on the shared cases of
//! `tests/dialects/dialect-set.cases`, which `lean/FirTest/DialectSet.lean`
//! reads too, so the two validators agree on each of them.
//!
//! The cases run with the core and a test dialect named `toy`: the type
//! `toy.flag`, the ops `toy.flag` and `toy.test`, and `toy.note`, which
//! takes any attributes and gives nothing, so an attribute can name a
//! dialect.

use funk_ir::dialects::core::{self, int_type, int_width};
use funk_ir::{
    Dialect, OpShape, OpSpec, OpTypes, Registry, Type, TypeCheck, TypeSpec, parse, print, verify,
};

const CASES: &str = include_str!("../../../tests/dialects/dialect-set.cases");

/// An op of the tagged dialect, with its decoding as a function.
struct TagOp(&'static str, fn(&OpTypes<'_>) -> bool);

impl OpSpec for TagOp {
    fn name(&self) -> &str {
        self.0
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if (self.1)(op) {
            Ok(OpShape::default())
        } else {
            Err(format!("{} used at the wrong types", self.0))
        }
    }
}

/// `toy.flag`.
struct Flag;

impl TypeSpec for Flag {
    fn check(&self, ty: &Type) -> Option<TypeCheck> {
        (ty.name == "toy.flag" && ty.args.is_none()).then_some(TypeCheck::Valid)
    }
}

fn is_flag(ty: &Type) -> bool {
    ty.name == "toy.flag" && ty.args.is_none()
}

fn registry() -> Registry {
    let mut r = Registry::core();
    r.register(
        Dialect::new("toy")
            .depends_on(core::NAME)
            .types(Flag)
            .op(TagOp("toy.flag", |o| {
                o.attrs.is_empty()
                    && matches!(o.operands, [t] if int_width(t).is_some())
                    && matches!(o.results, [r] if is_flag(r))
            }))
            .op(TagOp("toy.test", |o| {
                o.attrs.is_empty()
                    && matches!(o.operands, [t] if is_flag(t))
                    && o.results == [int_type(1)]
            }))
            .op(TagOp("toy.note", |o| {
                o.operands.is_empty() && o.results.is_empty()
            })),
    )
    .expect("the tagged dialect registers");
    r
}

struct Case {
    accept: bool,
    name: &'static str,
    text: &'static str,
}

fn cases() -> Vec<Case> {
    CASES
        .split("=== ")
        .skip(1)
        .map(|piece| {
            let (head, text) = piece.split_once('\n').expect("a case has a first line");
            let (verdict, name) = head.split_once(' ').expect("a verdict and a name");
            Case {
                accept: verdict == "accept",
                name,
                text,
            }
        })
        .collect()
}

#[test]
fn the_shared_cases_are_all_read() {
    let cases = cases();
    assert_eq!(cases.len(), 13);
    assert_eq!(cases.iter().filter(|c| c.accept).count(), 6);
}

#[test]
fn each_case_parses_prints_as_itself_and_gets_its_verdict() {
    let reg = registry();
    for c in cases() {
        let m = parse(c.text, &reg).unwrap_or_else(|e| panic!("{}: {e}", c.name));
        assert_eq!(print(&m), c.text, "{}", c.name);
        let ds = verify(&m, &reg);
        assert_eq!(ds.is_empty(), c.accept, "{}: {ds:#?}", c.name);
        for d in &ds {
            assert!(d.message.contains("dialect"), "{}: {d}", c.name);
        }
    }
}

#[test]
fn a_word_outside_the_set_names_its_function_and_dialect() {
    let reg = registry();
    let find = |name: &str| cases().into_iter().find(|c| c.name == name).unwrap();
    for (case, dialect) in [
        ("op-outside-the-set", "toy"),
        ("type-outside-the-set", "toy"),
        ("attribute-outside-the-set", "gpu"),
        ("nested-attribute-outside-the-set", "gpu"),
    ] {
        let ds = verify(&parse(find(case).text, &reg).unwrap(), &reg);
        assert_eq!(ds.len(), 1, "{case}: {ds:#?}");
        assert_eq!(
            ds[0].message,
            format!(
                "the function writes a word of the dialect {dialect}, which the module's dialect set does not name"
            ),
            "{case}"
        );
        assert!(ds[0].func.is_some() && ds[0].op.is_none(), "{case}");
    }
}

#[test]
fn the_core_registry_knows_no_dialect_to_name() {
    let reg = Registry::core();
    let m = parse(
        "dialects toy\n\nfunc @f() {\n^entry:\n  ret @0\n}\n\nlocs {\n  @0 = unknown\n}\n",
        &reg,
    )
    .unwrap();
    let ds = verify(&m, &reg);
    assert_eq!(ds.len(), 1, "{ds:#?}");
    assert_eq!(
        ds[0].message,
        "the dialect set names toy, which is not a known dialect"
    );
}

#[test]
fn a_built_module_prints_its_dialect_set_first() {
    let m = funk_ir::Module::new().dialect("toy").dialect("gpu");
    assert_eq!(print(&m), "dialects toy, gpu\n\nlocs {\n}\n");
    assert_eq!(print(&funk_ir::Module::new()), "locs {\n}\n");
}
