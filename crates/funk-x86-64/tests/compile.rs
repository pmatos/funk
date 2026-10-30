//! What `compile` gives for a module: the assembly of the object file and of
//! the entry point, or a diagnostic for each part it cannot lower.

use funk_ir::{LocRef, Module, Registry, parse};
use funk_x86_64::compile;

fn module(text: &str) -> Module {
    parse(text, &Registry::core()).unwrap()
}

const FLAG: &str = "func @flag(%x: i1) -> i1 {\n^entry:\n  ret %x @0\n}\n\nfunc @\"a b\"() {\n^entry:\n  ret @0\n}\n\nlocs {\n  @0 = unknown\n}\n";

#[test]
fn every_function_is_a_global_symbol_of_the_object_file() {
    let p = compile(&module(FLAG)).unwrap();
    for line in [
        "\t.globl\tflag\n",
        "\t.type\tflag, @function\n",
        "\t.globl\t__funk_sym_612062\n",
        "\t.section\t.note.GNU-stack,\"\",@progbits\n",
    ] {
        assert!(p.module.contains(line), "{line:?} not in\n{}", p.module);
    }
    assert!(!p.module.contains("__funk_start"));
    assert!(p.entry.contains("\t.globl\t__funk_start\n"));
    assert!(p.entry.contains("\tcall\t__funk_sym_612062\n"));
}

#[test]
fn an_i1_result_is_returned_as_zero_or_one() {
    let p = compile(&module(FLAG)).unwrap();
    let ret = "\tmovq\t-8(%rbp), %rax\n\tandl\t$1, %eax\n\tleave\n\tret\n";
    assert!(p.module.contains(ret), "{}", p.module);
}

#[test]
fn an_op_without_a_lowering_is_reported_at_the_op() {
    let mut m = module(FLAG);
    let f = m.items[0].as_func_mut().unwrap();
    f.body.blocks[0].ops[0].name = "toy.ret".into();
    f.body.blocks[0].ops[0].loc = LocRef(0);
    let ds = compile(&m).unwrap_err();
    assert_eq!(ds.len(), 1, "{ds:?}");
    assert_eq!(
        ds[0].message,
        "the x86-64 backend cannot lower the op toy.ret yet"
    );
    assert_eq!(
        (ds[0].func.as_deref(), ds[0].block.as_deref(), ds[0].op),
        (Some("flag"), Some("entry"), Some(0))
    );
    assert_eq!(ds[0].loc, Some(LocRef(0)));
}
