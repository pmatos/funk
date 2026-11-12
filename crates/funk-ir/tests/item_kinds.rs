//! Kinds of item that a dialect registers (ADR-2026-11-09-1543), on the
//! shared cases of `tests/dialects/item-kinds.cases`, which
//! `lean/FirTest/ItemKinds.lean` reads too, so the two validators agree on
//! each of them.
//!
//! The cases run with the core and a test dialect named `toy`, with the
//! type `toy.flag` and the kinds of item `toy.cell` and `toy.alias`, whose
//! rules are those of the Lean test dialect.

use funk_ir::dialects::core;
use funk_ir::registry::{ItemKindError, RegistryError};
use funk_ir::{
    Attr, Def, Dialect, DialectItem, FuncContext, Item, ItemKindSpec, Module, Registry, Type,
    TypeCheck, TypeSpec, parse, print, verify,
};

const CASES: &str = include_str!("../../../tests/dialects/item-kinds.cases");

/// `toy.flag`.
struct Flag;

impl TypeSpec for Flag {
    fn check(&self, ty: &Type) -> Option<TypeCheck> {
        (ty.name == "toy.flag" && ty.args.is_none()).then_some(TypeCheck::Valid)
    }
}

/// A `toy.cell` holds a flag: no parameters, the one result `toy.flag`,
/// and the one attribute 0 or 1.
struct Cell;

impl ItemKindSpec for Cell {
    fn name(&self) -> &str {
        "toy.cell"
    }

    fn check(&self, _cx: &FuncContext<'_>, item: &DialectItem) -> Result<(), String> {
        let flag = matches!(item.results.as_slice(), [t] if *t == Type::word("toy.flag"));
        let bit = matches!(item.attrs.as_slice(), [a] if *a == Attr::int(0) || *a == Attr::int(1));
        if item.params.is_empty() && flag && bit {
            Ok(())
        } else {
            Err("a cell holds a toy.flag, 0 or 1".to_string())
        }
    }
}

/// A `toy.alias` has no parameters or results, and names a function of its
/// table.
struct Alias;

impl ItemKindSpec for Alias {
    fn name(&self) -> &str {
        "toy.alias"
    }

    fn check(&self, cx: &FuncContext<'_>, item: &DialectItem) -> Result<(), String> {
        let names = match item.attrs.as_slice() {
            [Attr::Sym(s)] => cx.symbols.func_type(s).is_some(),
            _ => false,
        };
        if item.params.is_empty() && item.results.is_empty() && names {
            Ok(())
        } else {
            Err("an alias names a function of its table".to_string())
        }
    }
}

fn toy() -> Dialect {
    Dialect::new("toy")
        .depends_on(core::NAME)
        .types(Flag)
        .item_kind(Cell)
        .item_kind(Alias)
}

fn registry() -> Registry {
    let mut r = Registry::core();
    r.register(toy()).expect("the toy dialect registers");
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

fn messages(name: &str) -> Vec<String> {
    let reg = registry();
    let c = cases().into_iter().find(|c| c.name == name).unwrap();
    let m = parse(c.text, &reg).unwrap();
    verify(&m, &reg).into_iter().map(|d| d.message).collect()
}

/// A `toy.cell` whose parameter is a pointer of memory 1, after the layout
/// line `layout`, which may be empty; `lean/FirTest/ItemKinds.lean` checks
/// the same text.
fn ptr_cell(layout: &str) -> String {
    format!("dialects toy\n\n{layout}toy.cell @c(%x: ptr(1)) -> toy.flag 1 {{\n}}\n\nlocs {{\n}}\n")
}

#[test]
fn the_layout_declares_the_memories_of_an_items_types() {
    let reg = registry();
    let problems = |text: &str| -> Vec<(String, Option<String>)> {
        let m = parse(text, &reg).unwrap();
        verify(&m, &reg)
            .into_iter()
            .map(|d| (d.message, d.func))
            .collect()
    };
    let rule = (
        "the item breaks the rule of its kind \"toy.cell\": a cell holds a toy.flag, 0 or 1"
            .to_string(),
        Some("c".to_string()),
    );
    let undeclared = (
        "a type names memory 1, which the data layout does not declare".to_string(),
        Some("c".to_string()),
    );
    assert_eq!(problems(&ptr_cell("")), [rule.clone(), undeclared]);
    assert_eq!(
        problems(&ptr_cell(
            "layout memory(1, unit(8), pointer(32), little)\n\n"
        )),
        [rule]
    );
}

#[test]
fn the_shared_cases_are_all_read() {
    let cases = cases();
    assert_eq!(cases.len(), 16);
    assert_eq!(cases.iter().filter(|c| c.accept).count(), 4);
}

#[test]
fn each_case_parses_prints_as_itself_and_gets_its_verdict() {
    let reg = registry();
    for c in cases() {
        let m = parse(c.text, &reg).unwrap_or_else(|e| panic!("{}: {e}", c.name));
        assert_eq!(print(&m), c.text, "{}", c.name);
        let ds = verify(&m, &reg);
        assert_eq!(ds.is_empty(), c.accept, "{}: {ds:#?}", c.name);
    }
}

#[test]
fn a_kind_that_no_dialect_registers_has_no_rule_to_break() {
    assert_eq!(
        messages("unregistered-kind"),
        ["no dialect registers the kind of item \"toy.box\""]
    );
}

#[test]
fn the_rule_of_a_kind_is_its_dialects() {
    let ms = messages("cell-of-a-core-type");
    assert_eq!(ms.len(), 1, "{ms:?}");
    assert!(
        ms[0].starts_with("the item breaks the rule of its kind \"toy.cell\""),
        "{ms:?}"
    );
}

#[test]
fn the_kind_names_its_dialect_which_the_set_must_name() {
    assert_eq!(
        messages("nested-cell-does-not-inherit-the-set"),
        ["the item writes a word of the dialect toy, which the module's dialect set does not name"]
    );
}

#[test]
fn an_items_symbol_is_a_symbol_of_its_table() {
    assert_eq!(
        messages("symbol-of-a-function"),
        ["the symbol @c names more than one item"]
    );
}

#[test]
fn an_item_of_a_dialects_kind_has_an_empty_body() {
    let e = parse(
        "toy.cell @c() {\n^entry:\n  ret @0\n}\n\nlocs {\n}\n",
        &registry(),
    )
    .unwrap_err();
    assert_eq!((e.pos.line, e.pos.col), (1, 1));
    assert_eq!(e.reason, "an item of a dialect's kind has an empty body");
}

#[test]
fn any_reader_decodes_an_item_of_a_dialects_kind() {
    let text = "toy.cell @c() -> toy.flag 1 {\n}\n\nlocs {\n}\n";
    let e = parse(text, &Registry::core()).unwrap_err();
    assert!(e.reason.contains("toy.flag"), "{e}");
    let m = parse("toy.box @b() h(x) {\n}\n\nlocs {\n}\n", &Registry::core()).unwrap();
    let Some(Item::Dialect(i)) = m.items.first() else {
        panic!("{m:?}")
    };
    assert_eq!((i.kind.as_str(), i.attrs.len()), ("toy.box", 1));
}

#[test]
fn a_built_item_prints_as_its_kind_writes_it() {
    let mut cell = DialectItem::new("toy.cell", "c");
    cell.results.push(Type::word("toy.flag"));
    cell.attrs.push(Attr::int(1));
    let mut m = Module::new().dialect("toy");
    m.items.push(Item::Dialect(cell));
    let text = "dialects toy\n\ntoy.cell @c() -> toy.flag 1 {\n}\n\nlocs {\n}\n";
    assert_eq!(print(&m), text);
    assert!(verify(&m, &registry()).is_empty());
}

#[test]
fn a_built_item_obeys_the_general_rules() {
    let mut bad = DialectItem::new("cell", "c");
    bad.attrs.push(Attr::word("not a word"));
    let mut m = Module::new();
    m.items.push(Item::Dialect(bad));
    let ms: Vec<String> = verify(&m, &registry())
        .into_iter()
        .map(|d| d.message)
        .collect();
    assert_eq!(
        ms,
        [
            "the kind \"cell\" is not a word of a dialect",
            "an attribute of the item cannot be written",
            "no dialect registers the kind of item \"cell\"",
        ]
    );
}

#[test]
fn a_value_that_is_not_a_name_is_quoted_as_the_text_writes_it() {
    let mut cell = DialectItem::new("toy.cell", "c");
    for _ in 0..2 {
        cell.params.push(Def::new("a b", Type::word("i8")));
    }
    let mut m = Module::new().dialect("toy");
    m.items.push(Item::Dialect(cell));
    let ms: Vec<String> = verify(&m, &registry())
        .into_iter()
        .map(|d| d.message)
        .collect();
    assert_eq!(
        ms[..3],
        [
            "the parameter %\"a b\" is not a name",
            "the parameter %\"a b\" is not a name",
            "the item defines %\"a b\" more than once",
        ]
    );
}

/// A kind with the given word and no rule.
struct Kind(&'static str);

impl ItemKindSpec for Kind {
    fn name(&self) -> &str {
        self.0
    }

    fn check(&self, _cx: &FuncContext<'_>, _item: &DialectItem) -> Result<(), String> {
        Ok(())
    }
}

#[test]
fn registration_puts_each_kind_under_its_dialects_name() {
    let mut r = Registry::core();
    let outside = r.register(Dialect::new("toy").item_kind(Kind("gpu.cell")));
    assert_eq!(
        outside,
        Err(RegistryError::ItemKind(ItemKindError::OutsideDialect {
            dialect: "toy".into(),
            kind: "gpu.cell".into(),
        }))
    );
    let bare = r.register(Dialect::new("toy").item_kind(Kind("cell")));
    assert!(matches!(
        bare,
        Err(RegistryError::ItemKind(
            ItemKindError::OutsideDialect { .. }
        ))
    ));
    let twice = r.register(
        Dialect::new("toy")
            .item_kind(Kind("toy.a"))
            .item_kind(Kind("toy.a")),
    );
    assert_eq!(
        twice,
        Err(RegistryError::ItemKind(ItemKindError::Duplicate(
            "toy.a".into()
        )))
    );
    let mut core_kind = Registry::new();
    let core = core_kind.register(Dialect::new(core::NAME).item_kind(Kind("global")));
    assert!(matches!(
        core,
        Err(RegistryError::ItemKind(
            ItemKindError::OutsideDialect { .. }
        ))
    ));
    r.register(toy()).expect("the toy dialect registers");
    assert!(r.item_kind("toy.cell").is_some() && r.item_kind("toy.box").is_none());
}
