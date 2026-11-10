//! Region kinds that a dialect registers (ADR-2026-11-10-1941), on the same
//! texts as `lean/FirTest/RegionKinds.lean`.
//!
//! A test dialect named `toy` registers the kind `toy.graph`, whose rule asks
//! that a region hold exactly one block, and has two ops: `toy.run`, which
//! owns one region of the kind `toy.graph`, and `toy.free`, which owns one
//! region of the kind `toy.free`, which no dialect registers.

use funk_ir::dialects::core;
use funk_ir::registry::RegistryError;
use funk_ir::{
    Dialect, Func, FuncContext, OpShape, OpSpec, OpTypes, Region, RegionKindSpec, Registry, parse,
    print, verify,
};

/// An op with no attributes, operands or results that owns one region of
/// the kind `.1`.
struct Owner(&'static str, &'static str);

impl OpSpec for Owner {
    fn name(&self) -> &str {
        self.0
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        match (op.attrs, op.operands, op.results) {
            ([], [], []) => Ok(OpShape {
                regions: vec![self.1.to_string()],
                ..OpShape::default()
            }),
            _ => Err(format!("{} takes and gives nothing", self.0)),
        }
    }
}

/// The kind `.0`, whose rule asks that a region hold exactly one block.
struct OneBlock(&'static str);

impl RegionKindSpec for OneBlock {
    fn name(&self) -> &str {
        self.0
    }

    fn check(&self, _cx: &FuncContext<'_>, _func: &Func, region: &Region) -> Result<(), String> {
        match region.blocks.len() {
            1 => Ok(()),
            n => Err(format!("a region of {} holds one block, not {n}", self.0)),
        }
    }
}

fn toy() -> Dialect {
    Dialect::new("toy")
        .depends_on(core::NAME)
        .op(Owner("toy.run", "toy.graph"))
        .op(Owner("toy.free", "toy.free"))
        .region_kind(OneBlock("toy.graph"))
}

fn registry() -> Registry {
    let mut r = Registry::core();
    r.register(toy()).expect("the toy dialect registers");
    r
}

/// A module of one function whose entry block holds `ops`, then `ret`, with
/// the dialect set `toy` when `set`.
fn text(ops: &[&str], set: bool) -> String {
    let mut t = String::new();
    if set {
        t.push_str("dialects toy\n\n");
    }
    t.push_str("func @f() {\n^entry:\n");
    for op in ops {
        t.push_str(op);
        t.push('\n');
    }
    t.push_str("  ret @0\n}\n\nlocs {\n  @0 = unknown\n}\n");
    t
}

/// An op that owns one region whose blocks are `blocks`, each one `ret`,
/// written with the kind word `kind`.
fn owner(name: &str, kind: &str, blocks: &[&str]) -> String {
    let mut t = format!("  {name} {{{kind}\n");
    for l in blocks {
        t.push_str(&format!("    ^{l}:\n      ret @0\n"));
    }
    t.push_str("  } @0");
    t
}

/// The messages of the diagnostics of a text, which parses and prints as
/// itself.
fn messages(text: &str) -> Vec<String> {
    let reg = registry();
    let m = parse(text, &reg).unwrap_or_else(|e| panic!("{e}\n{text}"));
    assert_eq!(print(&m), text);
    verify(&m, &reg).into_iter().map(|d| d.message).collect()
}

#[test]
fn an_op_owns_regions_of_the_kinds_that_its_registration_states() {
    assert_eq!(
        messages(&text(&[&owner("toy.run", " toy.graph", &["g"])], true)),
        Vec::<String>::new()
    );
    assert_eq!(
        messages(&text(&[&owner("toy.run", "", &["g"])], true)),
        ["the regions of toy.run are not of the kinds that its registration states"]
    );
    assert_eq!(
        messages(&text(&[&owner("toy.run", " toy.free", &["g"])], true)),
        [
            "the regions of toy.run are not of the kinds that its registration states",
            "a region of toy.run is of kind toy.free, which no dialect registers",
        ]
    );
    assert_eq!(
        messages(&text(&[&owner("toy.free", " toy.free", &["g"])], true)),
        ["a region of toy.free is of kind toy.free, which no dialect registers"]
    );
}

#[test]
fn a_region_obeys_the_rule_of_its_kind() {
    assert_eq!(
        messages(&text(&[&owner("toy.run", " toy.graph", &["g", "h"])], true)),
        [
            "a region of toy.run breaks the rule of its kind toy.graph: a region of toy.graph holds one block, not 2"
        ]
    );
}

#[test]
fn an_op_inside_a_region_obeys_the_general_rules() {
    let call = "  toy.run { toy.graph\n    ^g:\n      call @nope @0\n      ret @0\n  } @0";
    assert_eq!(
        messages(&text(&[call], true)),
        [
            "op call refers to @nope, which names no function",
            "call @nope passes () and defines (), but no function is named @nope",
        ]
    );
    let loc = "  toy.run { toy.graph\n    ^g:\n      ret @7\n  } @0";
    assert_eq!(
        messages(&text(&[loc], true)),
        ["location reference @7 is not in the location table"]
    );
}

#[test]
fn a_region_kind_joins_the_dialect_set() {
    let word = "the function writes a word of the dialect toy, which the module's dialect set does not name";
    let br = "  br { toy.graph\n    ^g:\n      ret @0\n  } @0";
    let ms = messages(&text(&[br], false));
    assert!(ms.iter().any(|m| m == word), "{ms:?}");
    assert_eq!(
        messages(&text(&[&owner("toy.run", " toy.graph", &["g"])], false)),
        [word]
    );
}

#[test]
fn a_kind_is_registered_once_under_its_dialect_name() {
    let mut r = Registry::core();
    let outside = Dialect::new("toy")
        .depends_on(core::NAME)
        .region_kind(OneBlock("bit.graph"));
    assert_eq!(
        r.register(outside),
        Err(RegistryError::KindOutsideDialect {
            dialect: "toy".into(),
            kind: "bit.graph".into(),
        })
    );
    let bare = Dialect::new("toy").region_kind(OneBlock("graph"));
    assert!(matches!(
        r.register(bare),
        Err(RegistryError::KindOutsideDialect { .. })
    ));
    let twice = Dialect::new("toy")
        .region_kind(OneBlock("toy.graph"))
        .region_kind(OneBlock("toy.graph"));
    assert_eq!(
        r.register(twice),
        Err(RegistryError::DuplicateKind("toy.graph".into()))
    );
    assert!(r.region_kind("toy.graph").is_none());
    r.register(toy()).expect("the toy dialect registers");
    assert!(r.region_kind("toy.graph").is_some());
    assert!(r.region_kind("toy.free").is_none());
}
