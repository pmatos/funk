//! Large modules are checked in time linear in their size. Each input here
//! takes well under a second; a lookup that scans every block, or a
//! dominance query that walks the dominator tree, would take minutes.

use std::time::Instant;

use funk_ir::dialects::core::int_type;
use funk_ir::{Attr, Block, Func, Int, LocRef, Location, Module, Op, Registry, verify};

const L: LocRef = LocRef(0);

/// `@f` with `blocks` blocks in a chain, joined by an unregistered branch,
/// and `uses` uses in the last block of a value that the entry defines.
fn chain(blocks: usize, uses: usize) -> Module {
    let mut entry = Block::new("b0").op(Op::new("const", L)
        .attr(Attr::Int(Int::from(1)))
        .result("v", int_type(32)));
    let mut f = Func::new("f").result(int_type(32));
    for k in 1..blocks {
        entry = entry.op(Op::new("toy.br", L).succ(format!("b{k}"), &[]));
        f = f.block(entry);
        entry = Block::new(format!("b{k}"));
    }
    for j in 0..uses {
        entry = entry.op(Op::new("add", L)
            .operand("v")
            .operand("v")
            .result(format!("u{j}"), int_type(32)));
    }
    let mut m = Module::new();
    m.locs.push(Location::Unknown);
    m.func(f.block(entry.op(Op::new("ret", L).operand("v"))))
}

#[test]
fn long_chains_of_blocks_and_deep_dominance_verify_in_linear_time() {
    let (blocks, uses) = (60_000, 60_000);
    let m = chain(blocks, uses);
    let start = Instant::now();
    let ds = verify(&m, &Registry::core());
    let secs = start.elapsed().as_secs();
    assert_eq!(ds.len(), blocks - 1, "{:#?}", &ds[..3.min(ds.len())]);
    assert!(
        ds.iter()
            .all(|d| d.message == "op toy.br is not registered"),
        "{:#?}",
        &ds[..3]
    );
    assert!(secs < 20, "took {secs} s");
}
