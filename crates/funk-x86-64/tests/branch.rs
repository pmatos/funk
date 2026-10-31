//! How `br` and `cond_br` are lowered (#19): blocks in the order of the
//! body, each at its label, a jump unless the successor comes next
//! (ADR-2026-10-31-0334), a test of bit 0 of the condition
//! (ADR-2026-10-30-1231), and the values a successor passes copied into its
//! block's arguments as one parallel move (ADR-2026-10-31-0335).

use funk_ir::{LocRef, Registry, parse};
use funk_x86_64::compile;

/// The assembly of the functions `funcs`, each with its ops at `@0`.
fn lowered(funcs: &str) -> String {
    let text = format!("{funcs}\nlocs {{\n  @0 = unknown\n}}\n");
    let m = parse(&text, &Registry::core()).unwrap_or_else(|e| panic!("{e}\n{text}"));
    compile(&m).unwrap_or_else(|ds| panic!("{ds:#?}")).module
}

/// The instructions `lines`, each on a line of its own, and the labels,
/// which end with `:`, on lines of their own.
fn code(lines: &[&str]) -> String {
    let mut out = String::new();
    for l in lines {
        if l.ends_with(':') {
            out += &format!("{l}\n");
        } else {
            out += &format!("\t{l}\n");
        }
    }
    out
}

fn assert_has(asm: &str, lines: &[&str]) {
    let want = code(lines);
    assert!(asm.contains(&want), "{want}\nnot in\n{asm}");
}

/// A loop that swaps two `i32` while `%c` holds. The slots are `%a` at
/// `-8`, `%b` at `-16`, `%c` at `-24`, `%x` at `-32`, `%y` at `-40` and `%r`
/// at `-48`.
const SWAP: &str = "func @f(%a: i32, %b: i32, %c: i1) -> i32 {
^entry:
  br ^loop(%a, %b) @0
^loop(%x: i32, %y: i32):
  cond_br %c, ^loop(%y, %x), ^exit(%x) @0
^exit(%r: i32):
  ret %r @0
}
";

#[test]
fn a_swap_goes_through_rcx_and_each_edge_moves_its_own_values() {
    assert_has(
        &lowered(SWAP),
        &[
            "# br ^loop(%a, %b) @0",
            "movq\t-8(%rbp), %rax",
            "movq\t%rax, -32(%rbp)",
            "movq\t-16(%rbp), %rax",
            "movq\t%rax, -40(%rbp)",
            ".Lb0_loop:",
            "# cond_br %c, ^loop(%y, %x), ^exit(%x) @0",
            "movq\t-24(%rbp), %rax",
            "testb\t$1, %al",
            "jz\t.Lc0_1",
            "movq\t-32(%rbp), %rcx",
            "movq\t-40(%rbp), %rax",
            "movq\t%rax, -32(%rbp)",
            "movq\t%rcx, -40(%rbp)",
            "jmp\t.Lb0_loop",
            ".Lc0_1:",
            "movq\t-32(%rbp), %rax",
            "movq\t%rax, -48(%rbp)",
            ".Lb0_exit:",
        ],
    );
}

#[test]
fn a_rotation_saves_one_slot_and_a_value_may_go_to_several_arguments() {
    let rotate = "func @f(%a: i8, %b: i8, %c: i8) -> i8 {
^entry:
  br ^loop(%a, %b, %c) @0
^loop(%x: i8, %y: i8, %z: i8):
  br ^loop(%y, %z, %x) @0
}
";
    // %x at -32, %y at -40, %z at -48.
    assert_has(
        &lowered(rotate),
        &[
            "# br ^loop(%y, %z, %x) @0",
            "movq\t-32(%rbp), %rcx",
            "movq\t-40(%rbp), %rax",
            "movq\t%rax, -32(%rbp)",
            "movq\t-48(%rbp), %rax",
            "movq\t%rax, -40(%rbp)",
            "movq\t%rcx, -48(%rbp)",
            "jmp\t.Lb0_loop",
        ],
    );
    let fan = rotate.replace("br ^loop(%y, %z, %x)", "br ^loop(%x, %x, %x)");
    assert_has(
        &lowered(&fan),
        &[
            "# br ^loop(%x, %x, %x) @0",
            "movq\t-32(%rbp), %rax",
            "movq\t%rax, -40(%rbp)",
            "movq\t-32(%rbp), %rax",
            "movq\t%rax, -48(%rbp)",
            "jmp\t.Lb0_loop",
        ],
    );
}

/// The code from the test of `@h(%c: i1, %a: i16)`'s `cond_br` `term` to
/// the label of the block after it, with the blocks `order` after the
/// entry, each returning. `%a` is at `-16`, and the blocks' arguments
/// follow it in their order.
fn cond(term: &str, order: [&str; 3]) -> String {
    let mut text = format!("func @h(%c: i1, %a: i16) {{\n^entry:\n  {term} @0\n");
    for b in order {
        text += &format!("^{b}:\n  ret @0\n");
    }
    let asm = lowered(&(text + "}\n"));
    let start = asm.find("\ttestb").expect("a test");
    let end = asm[start..].find("\n.Lb0_").expect("a block") + start + 1;
    asm[start..end].to_string()
}

#[test]
fn a_cond_br_without_moves_jumps_straight_to_its_blocks() {
    let test = "testb\t$1, %al";
    assert_eq!(
        cond("cond_br %c, ^t, ^e", ["t", "e", "o"]),
        code(&[test, "jz\t.Lb0_e"])
    );
    assert_eq!(
        cond("cond_br %c, ^t, ^e", ["e", "t", "o"]),
        code(&[test, "jnz\t.Lb0_t"])
    );
    assert_eq!(
        cond("cond_br %c, ^t, ^e", ["o", "t", "e"]),
        code(&[test, "jnz\t.Lb0_t", "jmp\t.Lb0_e"])
    );
}

#[test]
fn a_cond_br_lays_out_its_edges_so_that_the_next_block_may_follow() {
    let test = "testb\t$1, %al";
    // Only ^t's edge moves: the jump goes straight to ^e.
    assert_eq!(
        cond("cond_br %c, ^t(%a), ^e", ["o", "t(%x: i16)", "e"]),
        code(&[
            test,
            "jz\t.Lb0_e",
            "movq\t-16(%rbp), %rax",
            "movq\t%rax, -24(%rbp)",
            "jmp\t.Lb0_t",
        ])
    );
    // Only ^e's edge moves, and ^e comes next.
    assert_eq!(
        cond("cond_br %c, ^t, ^e(%a)", ["e(%y: i16)", "t", "o"]),
        code(&[
            test,
            "jnz\t.Lb0_t",
            "movq\t-16(%rbp), %rax",
            "movq\t%rax, -24(%rbp)"
        ])
    );
    // Both edges move and ^t comes next: ^e's edge goes first and jumps,
    // and ^t's ends the branch.
    assert_eq!(
        cond(
            "cond_br %c, ^t(%a), ^e(%a)",
            ["t(%x: i16)", "e(%y: i16)", "o"]
        ),
        code(&[
            test,
            "jnz\t.Lc0_1",
            "movq\t-16(%rbp), %rax",
            "movq\t%rax, -32(%rbp)",
            "jmp\t.Lb0_e",
            ".Lc0_1:",
            "movq\t-16(%rbp), %rax",
            "movq\t%rax, -24(%rbp)",
        ])
    );
}

#[test]
fn a_br_to_the_next_block_falls_through() {
    let text = "func @f(%a: i64) -> i64 {
^entry:
  br ^b @0
^c:
  ret %a @0
^b:
  br ^d @0
^d:
  br ^c @0
}
";
    let asm = lowered(text);
    for (br, after) in [
        ("^b", "\tjmp\t.Lb0_b\n.Lb0_c:\n"),
        ("^d", ".Lb0_d:\n"),
        ("^c", "\tjmp\t.Lb0_c\n\t.size\t"),
    ] {
        let want = format!("\t# br {br} @0\n{after}");
        assert!(asm.contains(&want), "{want}\nnot in\n{asm}");
    }
}

#[test]
fn each_function_has_labels_of_its_own() {
    let one = "func @f() {\n^entry:\n  br ^b @0\n^b:\n  ret @0\n}\n";
    let two = one.replace("@f", "@g");
    let asm = lowered(&format!("{one}\n{two}"));
    assert!(
        asm.contains(".Lb0_b:\n") && asm.contains(".Lb1_b:\n"),
        "{asm}"
    );
}

#[test]
fn a_block_argument_of_a_width_the_backend_lacks_is_reported_once() {
    let text = "func @f(%a: i8) -> i8 {
^entry:
  %w: i128 = zext %a @0
  br ^b(%w, %a) @0
^b(%x: i128, %y: i8):
  ret %y @0
}

locs {
  @0 = unknown
}
";
    let ds = compile(&parse(text, &Registry::core()).unwrap()).unwrap_err();
    let at: Vec<_> = ds
        .iter()
        .map(|d| (d.block.as_deref(), d.op, d.loc))
        .collect();
    assert_eq!(
        at,
        [
            (Some("entry"), Some(0), Some(LocRef(0))),
            (Some("b"), None, Some(LocRef(0)))
        ],
        "{ds:#?}"
    );
    assert!(ds[1].message.starts_with("block argument %x: "), "{ds:#?}");
}
