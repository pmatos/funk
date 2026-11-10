//! The registry routes each op and type by the dialect that its word names
//! (ADR-2026-11-09-1543): `name.word` belongs to the dialect `name`, and a
//! bare word to the core. Registration checks that a dialect writes its ops
//! under its own name and that the dialects it depends on are registered.

use funk_ir::dialects::core;
use funk_ir::registry::RegistryError;
use funk_ir::{Dialect, OpShape, OpSpec, OpTypes, Registry, Type, TypeCheck, TypeSpec};

struct Named(&'static str);

impl OpSpec for Named {
    fn name(&self) -> &str {
        self.0
    }

    fn decode(&self, _: &OpTypes<'_>) -> Result<OpShape, String> {
        Ok(OpShape::default())
    }
}

fn toy() -> Dialect {
    Dialect::new("toy").depends_on(core::NAME)
}

#[test]
fn registration_rejects_names_that_collide_or_cannot_be_written() {
    let mut r = Registry::core();
    assert_eq!(
        r.register(Dialect::new("toy").op(Named("add"))),
        Err(RegistryError::OpOutsideDialect {
            dialect: "toy".into(),
            op: "add".into()
        })
    );
    assert_eq!(
        r.register(toy().op(Named("toy op"))),
        Err(RegistryError::OpNameNotAWord("toy op".into()))
    );
    assert_eq!(
        r.register(toy().op(Named("toy.a")).op(Named("toy.a"))),
        Err(RegistryError::DuplicateOp("toy.a".into()))
    );
    assert_eq!(
        r.register(Dialect::new("core")),
        Err(RegistryError::DuplicateDialect("core".into()))
    );
    assert!(
        r.op("toy.a").is_none(),
        "a failed registration changes nothing"
    );
    assert_eq!(r.register(toy().op(Named("toy.a"))), Ok(()));
    assert_eq!(r.dialect_of("toy.a"), Some("toy"));
}

#[test]
fn a_dialect_writes_its_ops_under_its_own_name() {
    let mut r = Registry::core();
    for op in ["fine.a", "toyx.a", "to.a"] {
        assert_eq!(
            r.register(toy().op(Named(op))),
            Err(RegistryError::OpOutsideDialect {
                dialect: "toy".into(),
                op: op.into()
            }),
            "{op}"
        );
    }
    assert_eq!(r.register(toy().op(Named("toy.a.b"))), Ok(()));
    assert_eq!(r.dialect_of("toy.a.b"), Some("toy"));
}

#[test]
fn the_core_writes_bare_words() {
    let mut r = Registry::new();
    assert_eq!(
        r.register(Dialect::new(core::NAME).op(Named("core.add"))),
        Err(RegistryError::OpOutsideDialect {
            dialect: "core".into(),
            op: "core.add".into()
        })
    );
    assert_eq!(r.register(core::dialect()), Ok(()));
    assert_eq!(r.dialect_of("add"), Some("core"));
}

#[test]
fn a_dialect_name_is_a_word_without_a_dot() {
    let mut r = Registry::core();
    for name in ["toy.x", "", "1toy", "a b"] {
        assert_eq!(
            r.register(Dialect::new(name)),
            Err(RegistryError::DialectNameNotAPrefix(name.into())),
            "{name:?}"
        );
    }
}

#[test]
fn a_dependency_must_be_registered_first() {
    let mut r = Registry::new();
    assert_eq!(
        r.register(toy().op(Named("toy.a"))),
        Err(RegistryError::MissingDependency {
            dialect: "toy".into(),
            dependency: "core".into()
        })
    );
    assert!(r.op("toy.a").is_none());
    assert_eq!(r.register(core::dialect()), Ok(()));
    assert_eq!(r.register(toy().op(Named("toy.a"))), Ok(()));
    assert_eq!(r.dependencies("toy"), Some(&["core".to_string()][..]));
    assert_eq!(r.dependencies("core"), Some(&[][..]));
    assert_eq!(r.dependencies("gpu"), None);
    let gpu = Dialect::new("gpu").depends_on("toy").depends_on("core");
    assert_eq!(r.register(gpu), Ok(()));
    assert_eq!(
        r.register(Dialect::new("self").depends_on("self")),
        Err(RegistryError::MissingDependency {
            dialect: "self".into(),
            dependency: "self".into()
        })
    );
}

/// A type family that claims every type it is asked about.
struct Greedy;

impl TypeSpec for Greedy {
    fn check(&self, _: &Type) -> Option<TypeCheck> {
        Some(TypeCheck::Invalid("claimed by toy".into()))
    }
}

#[test]
fn a_type_goes_only_to_the_dialect_its_head_word_names() {
    let mut r = Registry::core();
    r.register(toy().types(Greedy)).expect("toy registers");
    assert_eq!(r.check_type(&Type::word("i32")), TypeCheck::Valid);
    assert_eq!(
        r.check_type(&Type::word("toy.tok")),
        TypeCheck::Invalid("claimed by toy".into())
    );
    assert_eq!(
        r.check_type(&Type::app("toy.vec", vec![])),
        TypeCheck::Invalid("claimed by toy".into())
    );
    let TypeCheck::Malformed(why) = r.check_type(&Type::word("gpu.mem")) else {
        panic!("a type of a dialect that is not registered does not decode");
    };
    assert!(why.contains("no dialect named gpu is registered"), "{why}");
    let TypeCheck::Malformed(why) = r.check_type(&Type::word("u8")) else {
        panic!("a bare word that the core does not claim does not decode");
    };
    assert!(why.contains("u8 is not a type of core"), "{why}");
    let TypeCheck::Malformed(why) = Registry::new().check_type(&Type::word("i8")) else {
        panic!("a bare word does not decode without the core");
    };
    assert!(why.contains("no dialect named core is registered"), "{why}");
}

#[test]
fn a_dialect_that_claims_no_type_leaves_its_words_undecoded() {
    let mut r = Registry::core();
    r.register(toy()).expect("toy registers");
    let TypeCheck::Malformed(why) = r.check_type(&Type::word("toy.tok")) else {
        panic!("toy has no types");
    };
    assert!(why.contains("toy.tok is not a type of toy"), "{why}");
}
