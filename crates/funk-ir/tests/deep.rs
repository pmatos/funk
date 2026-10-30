//! fir has no nesting limit (ADR-2026-10-30-1333). Texts and IR nested ten
//! million levels deep, in attributes, regions and items, parse, print,
//! verify, clone, compare, hash, debug-format and drop on a thread with a
//! 256 KiB stack, where a walk that recursed once per level would overflow
//! within a few thousand levels.
//!
//! What a test costs grows with the size of what it holds, not with its
//! depth: ten million levels of regions take 3.3 GB of IR, so the tests that
//! hold two copies of nested regions, or print them, run less deep.

use std::fmt::{self, Debug, Write};
use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::Mutex;

use funk_ir::{
    Attr, Block, Dialect, Module, OpShape, OpSpec, OpTypes, Registry, parse, print, verify,
};

const DEPTH: usize = 10_000_000;

/// Runs `f` on a thread with a 256 KiB stack. One test runs at a time, as
/// each holds gigabytes at this depth.
fn on_small_stack(f: impl FnOnce() + Send + 'static) {
    static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());
    let _one = ONE_AT_A_TIME.lock().unwrap_or_else(|e| e.into_inner());
    let thread = std::thread::Builder::new().stack_size(256 << 10).spawn(f);
    if let Err(panic) = thread.expect("a thread").join() {
        std::panic::resume_unwind(panic);
    }
}

/// `toy.nest`: an op with any attributes and regions, and no values.
struct ToyNest;

impl OpSpec for ToyNest {
    fn name(&self) -> &str {
        "toy.nest"
    }

    fn decode(&self, op: &OpTypes<'_>) -> Result<OpShape, String> {
        if op.operands.is_empty() && op.results.is_empty() {
            Ok(OpShape::default())
        } else {
            Err("toy.nest defines and uses no values".into())
        }
    }
}

fn registry() -> Registry {
    let mut reg = Registry::core();
    reg.register(Dialect::new("toy").op(ToyNest))
        .expect("the toy dialect registers");
    reg
}

/// `@f` with `body` in its entry block, before `ret`, in a module whose
/// table has `@0`.
fn module_text(body: &str) -> String {
    format!("func @f() {{\n^e:\n{body}  ret @0\n}}\n\nlocs {{\n  @0 = unknown\n}}\n")
}

/// A text of `depth` attributes, each applying `h` to the next.
fn attr_text(depth: usize) -> String {
    let attr = format!("{}x{}", "h(".repeat(depth), ")".repeat(depth));
    module_text(&format!("  toy.nest {attr} @0\n"))
}

/// A text of `depth` regions, each holding a block whose op holds the next,
/// written without indentation.
fn region_text(depth: usize) -> String {
    module_text(&format!(
        "{}{}",
        "toy.nest {\n^e:\n".repeat(depth),
        "} @0\n".repeat(depth)
    ))
}

fn hash(x: &impl Hash) -> u64 {
    let mut h = DefaultHasher::new();
    x.hash(&mut h);
    h.finish()
}

/// Hashes the text written to it, so that a debug form gigabytes long is
/// compared without being kept.
#[derive(Default)]
struct Digest(DefaultHasher, usize);

impl Write for Digest {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0.write(s.as_bytes());
        self.1 += s.len();
        Ok(())
    }
}

/// The hash and the length of the debug form of `x`.
fn debug_digest(x: &impl Debug) -> (u64, usize) {
    let mut d = Digest::default();
    write!(d, "{x:?}").expect("a digest takes any text");
    (d.0.finish(), d.1)
}

/// The length of the debug form of the module that `text(depth)` parses to,
/// which grows by the same amount with each level.
fn debug_len(text: fn(usize) -> String, depth: usize) -> usize {
    let len = |d| debug_digest(&parse(&text(d), &registry()).expect("a text")).1;
    len(1) + (depth - 1) * (len(2) - len(1))
}

/// Clones, compares, hashes and debug-formats `m`, which `text(depth)`
/// parses to, and changes the clone at its deepest point with `change` to
/// check that the comparison reaches it.
fn copies_and_compares(
    m: &Module,
    text: fn(usize) -> String,
    depth: usize,
    change: fn(&mut Module),
) {
    let mut copy = m.clone();
    assert!(copy == *m);
    assert_eq!(hash(&copy), hash(m));
    let digest = debug_digest(m);
    assert_eq!(digest, debug_digest(&copy));
    assert_eq!(digest.1, debug_len(text, depth));
    change(&mut copy);
    assert!(copy != *m);
}

/// The innermost attribute of `a`, which nests applications of one
/// argument.
fn innermost(mut a: &mut Attr) -> &mut Attr {
    loop {
        match a {
            Attr::App(_, args) => a = &mut args[0],
            leaf => return leaf,
        }
    }
}

/// The innermost block of `b`, whose ops each hold one region of one block.
fn innermost_block(mut b: &mut Block) -> &mut Block {
    while !b.ops.is_empty() {
        b = &mut b.ops[0].regions[0].blocks[0];
    }
    b
}

fn entry(m: &mut Module) -> &mut Block {
    let f = m.items[0].as_func_mut().expect("a function");
    &mut f.body.blocks[0]
}

#[test]
fn attributes_nest_to_any_depth() {
    on_small_stack(|| {
        let text = attr_text(DEPTH);
        let reg = registry();
        let m = parse(&text, &reg).expect("the text parses");
        assert!(print(&m) == text);
        drop(text);
        assert_eq!(verify(&m, &reg), vec![]);
        copies_and_compares(&m, attr_text, DEPTH, |m| {
            *innermost(&mut entry(m).ops[0].attrs[0]) = Attr::word("y");
        });
    });
}

#[test]
fn regions_nest_to_any_depth() {
    on_small_stack(|| {
        let text = region_text(DEPTH);
        let reg = registry();
        let m = parse(&text, &reg).expect("the text parses");
        drop(text);
        let ds = verify(&m, &reg);
        assert_eq!(ds.len(), 1, "{ds:?}");
        assert!(ds[0].message.contains("owns a region"), "{ds:?}");
        std::hint::black_box(hash(&m));
        assert_eq!(debug_digest(&m).1, debug_len(region_text, DEPTH));
    });
}

/// A clone and the walks that compare it with its original take as much
/// again as the original, so regions are copied a million levels deep.
#[test]
fn regions_copy_and_compare_at_any_depth() {
    on_small_stack(|| {
        let depth = 1_000_000;
        let m = parse(&region_text(depth), &registry()).expect("the text parses");
        copies_and_compares(&m, region_text, depth, |m| {
            let inner = innermost_block(&mut entry(m).ops[0].regions[0].blocks[0]);
            inner.label = "f".into();
        });
    });
}

/// The canonical text of regions grows with the square of their depth, as
/// each level is indented two spaces deeper than the last, so they are
/// printed at a depth whose text takes tens of megabytes.
#[test]
fn regions_print_at_any_depth() {
    on_small_stack(|| {
        let depth = 3_000;
        let mut body = String::new();
        for k in 0..depth {
            let n = 2 + 4 * k;
            body.push_str(&format!("{:n$}toy.nest {{\n{:m$}^e:\n", "", "", m = n + 2));
        }
        for k in (0..depth).rev() {
            body.push_str(&format!("{:n$}}} @0\n", "", n = 2 + 4 * k));
        }
        let text = module_text(&body);
        let m = parse(&text, &registry()).expect("the text parses");
        assert!(print(&m) == text);
    });
}

#[test]
fn items_nest_to_any_depth() {
    on_small_stack(|| {
        let items = format!("{}{}", "func @f() {\n".repeat(DEPTH), "}\n".repeat(DEPTH));
        let e = parse(&format!("{items}\nlocs {{\n}}\n"), &registry()).unwrap_err();
        assert_eq!((e.pos.line, e.pos.col), (2, 1), "{e}");
        assert!(e.reason.contains("holds blocks, not items"), "{e}");
    });
}
