//! How ops at `i128` are lowered (#21): each value is a pair of slots, its
//! low half at the lower address, and each op works on a pair of registers
//! (`docs/decisions/x86-64-backend-lowering.md#lowering-i128`); calls pass
//! an `i128` in two registers or in 16 aligned bytes of the stack, and
//! return it in `%rdx:%rax`
//! (`docs/decisions/x86-64-backend-abi.md#arguments`).

use funk_ir::dialects::core::WRAP_FLAG_SETS;
use funk_ir::{Registry, parse};
use funk_x86_64::compile;

/// The assembly of the functions `funcs`.
fn lowered(funcs: &str) -> String {
    let text = format!("{funcs}\nlocs {{\n  @0 = unknown\n}}\n");
    compile(&parse(&text, &Registry::core()).unwrap_or_else(|e| panic!("{e}\n{text}")))
        .unwrap_or_else(|ds| panic!("{ds:#?}"))
        .module
}

/// The assembly of `@f(%a: i128, %b: i128) -> TY` with the one op `line`,
/// whose result is `%r`. `%a` is at `-16(%rbp)` and `-8(%rbp)`, `%b` at
/// `-32(%rbp)` and `-24(%rbp)`, and `%r` next.
fn binary(ty: &str, line: &str) -> String {
    lowered(&format!(
        "func @f(%a: i128, %b: i128) -> {ty} {{\n^entry:\n  {line} @0\n  ret %r @0\n}}\n"
    ))
}

/// Checks that `asm` holds the comment of `line` and then `code`, one
/// instruction a line, up to the comment of `ret %r`.
fn assert_op(asm: &str, line: &str, code: &[&str]) {
    let body: String = code.iter().map(|l| format!("\t{l}\n")).collect();
    let want = format!("\t# {line} @0\n{body}\t# ret %r @0\n");
    assert!(asm.contains(&want), "{want}\nnot in\n{asm}");
}

/// The loads of `%a` and the stores of a result `%r` at `i128`.
const LOAD_A: [&str; 2] = ["movq\t-16(%rbp), %rax", "movq\t-8(%rbp), %rdx"];
const STORE_R: [&str; 2] = ["movq\t%rax, -48(%rbp)", "movq\t%rdx, -40(%rbp)"];

fn with_a(middle: &[&str]) -> Vec<String> {
    LOAD_A
        .iter()
        .chain(middle)
        .chain(&STORE_R)
        .map(|s| s.to_string())
        .collect()
}

fn strs(v: &[String]) -> Vec<&str> {
    v.iter().map(String::as_str).collect()
}

#[test]
fn add_and_sub_carry_and_borrow_into_the_high_half_whatever_their_flags() {
    for (op, low, high) in [("add", "addq", "adcq"), ("sub", "subq", "sbbq")] {
        for flags in WRAP_FLAG_SETS {
            let words: Vec<&str> = std::iter::once(op).chain(flags.iter().copied()).collect();
            let line = format!("%r: i128 = {} %a, %b", words.join(" "));
            let lo = format!("{low}\t-32(%rbp), %rax");
            let hi = format!("{high}\t-24(%rbp), %rdx");
            let code = with_a(&[&lo, &hi]);
            assert_op(&binary("i128", &line), &line, &strs(&code));
        }
    }
}

#[test]
fn mul_adds_the_cross_products_into_the_high_half_of_the_low_product() {
    for flags in WRAP_FLAG_SETS {
        let words: Vec<&str> = std::iter::once("mul")
            .chain(flags.iter().copied())
            .collect();
        let line = format!("%r: i128 = {} %a, %b", words.join(" "));
        let code = [
            "movq\t-16(%rbp), %rax",
            "mulq\t-32(%rbp)",
            "movq\t-16(%rbp), %rcx",
            "imulq\t-24(%rbp), %rcx",
            "addq\t%rcx, %rdx",
            "movq\t-8(%rbp), %rcx",
            "imulq\t-32(%rbp), %rcx",
            "addq\t%rcx, %rdx",
            STORE_R[0],
            STORE_R[1],
        ];
        assert_op(&binary("i128", &line), &line, &code);
    }
}

#[test]
fn bitwise_ops_apply_to_each_half() {
    for (op, mnemonic) in [("and", "andq"), ("or", "orq"), ("xor", "xorq")] {
        let line = format!("%r: i128 = {op} %a, %b");
        let lo = format!("{mnemonic}\t-32(%rbp), %rax");
        let hi = format!("{mnemonic}\t-24(%rbp), %rdx");
        assert_op(&binary("i128", &line), &line, &strs(&with_a(&[&lo, &hi])));
    }
}

/// The amount's low half is in `%rcx`; bit 6 of `%cl` moves the halves one
/// place further, with no branch.
#[test]
fn shifts_shift_both_halves_and_move_them_at_64_or_more() {
    let load_n = "movq\t-32(%rbp), %rcx";
    let tail = ["testb\t$64, %cl"];
    for (op, middle) in [
        (
            "shl",
            vec![
                load_n,
                "shldq\t%cl, %rax, %rdx",
                "shlq\t%cl, %rax",
                "xorl\t%esi, %esi",
                tail[0],
                "cmovneq\t%rax, %rdx",
                "cmovneq\t%rsi, %rax",
            ],
        ),
        (
            "lshr",
            vec![
                load_n,
                "shrdq\t%cl, %rdx, %rax",
                "shrq\t%cl, %rdx",
                "xorl\t%esi, %esi",
                tail[0],
                "cmovneq\t%rdx, %rax",
                "cmovneq\t%rsi, %rdx",
            ],
        ),
        (
            "ashr",
            vec![
                load_n,
                "shrdq\t%cl, %rdx, %rax",
                "movq\t%rdx, %rsi",
                "sarq\t$63, %rsi",
                "sarq\t%cl, %rdx",
                tail[0],
                "cmovneq\t%rdx, %rax",
                "cmovneq\t%rsi, %rdx",
            ],
        ),
    ] {
        let line = format!("%r: i128 = {op} %a, %b");
        assert_op(&binary("i128", &line), &line, &strs(&with_a(&middle)));
    }
}

/// `eq` and `ne` test whether the halves' differences are both zero; the
/// ordering predicates subtract with a borrow, swapping the operands for
/// `>` and `<=`, and read only flags that the borrow chain sets.
#[test]
fn icmp_reads_the_whole_subtraction() {
    let store = "movq\t%rax, -40(%rbp)";
    for (p, set) in [("eq", "sete"), ("ne", "setne")] {
        let line = format!("%r: i1 = icmp {p} %a, %b");
        let code = [
            LOAD_A[0],
            LOAD_A[1],
            "xorq\t-32(%rbp), %rax",
            "xorq\t-24(%rbp), %rdx",
            "orq\t%rdx, %rax",
            &format!("{set}\t%al"),
            store,
        ];
        assert_op(&binary("i1", &line), &line, &code);
    }
    let a = ["-16(%rbp)", "-8(%rbp)"];
    let b = ["-32(%rbp)", "-24(%rbp)"];
    for (p, swap, set) in [
        ("slt", false, "setl"),
        ("sge", false, "setge"),
        ("sgt", true, "setl"),
        ("sle", true, "setge"),
        ("ult", false, "setb"),
        ("uge", false, "setae"),
        ("ugt", true, "setb"),
        ("ule", true, "setae"),
    ] {
        let (x, y) = if swap { (b, a) } else { (a, b) };
        let line = format!("%r: i1 = icmp {p} %a, %b");
        let code = [
            format!("movq\t{}, %rax", x[0]),
            format!("movq\t{}, %rdx", x[1]),
            format!("cmpq\t{}, %rax", y[0]),
            format!("sbbq\t{}, %rdx", y[1]),
            format!("{set}\t%al"),
            store.to_string(),
        ];
        assert_op(&binary("i1", &line), &line, &strs(&code));
    }
}

#[test]
fn select_moves_in_each_half_of_its_second_value() {
    let asm = lowered(
        "func @f(%c: i1, %a: i128, %b: i128) -> i128 {\n^entry:\n  %r: i128 = select %c, %a, %b @0\n  ret %r @0\n}\n",
    );
    let code = [
        "movq\t-8(%rbp), %rcx",
        "movq\t-24(%rbp), %rax",
        "movq\t-16(%rbp), %rdx",
        "testb\t$1, %cl",
        "cmovzq\t-40(%rbp), %rax",
        "cmovzq\t-32(%rbp), %rdx",
        "movq\t%rax, -56(%rbp)",
        "movq\t%rdx, -48(%rbp)",
    ];
    assert_op(&asm, "%r: i128 = select %c, %a, %b", &code);
}

#[test]
fn width_changes_fill_or_drop_the_high_half() {
    for (op, m, middle) in [
        ("zext", 8, vec!["movzbl\t%al, %eax", "xorl\t%edx, %edx"]),
        ("zext", 64, vec!["xorl\t%edx, %edx"]),
        (
            "sext",
            1,
            vec![
                "shlq\t$63, %rax",
                "sarq\t$63, %rax",
                "movq\t%rax, %rdx",
                "sarq\t$63, %rdx",
            ],
        ),
        (
            "sext",
            32,
            vec!["movslq\t%eax, %rax", "movq\t%rax, %rdx", "sarq\t$63, %rdx"],
        ),
    ] {
        let line = format!("%r: i128 = {op} %a");
        let asm = lowered(&format!(
            "func @f(%a: i{m}) -> i128 {{\n^entry:\n  {line} @0\n  ret %r @0\n}}\n"
        ));
        let code: Vec<&str> = std::iter::once("movq\t-8(%rbp), %rax")
            .chain(middle)
            .chain(["movq\t%rax, -24(%rbp)", "movq\t%rdx, -16(%rbp)"])
            .collect();
        assert_op(&asm, &line, &code);
    }
    for n in [1, 8, 64] {
        let line = format!("%r: i{n} = trunc %a");
        let asm = lowered(&format!(
            "func @f(%a: i128) -> i{n} {{\n^entry:\n  {line} @0\n  ret %r @0\n}}\n"
        ));
        let code = ["movq\t-16(%rbp), %rax", "movq\t%rax, -24(%rbp)"];
        assert_op(&asm, &line, &code);
    }
}

#[test]
fn freeze_copies_both_halves_into_its_own_slots() {
    let line = "%r: i128 = freeze %a";
    let code = with_a(&[]);
    assert_op(&binary("i128", line), line, &strs(&code));
}

#[test]
fn a_constant_is_its_low_and_its_high_64_bits() {
    for (v, lo, hi) in [
        ("0", "movq\t$0, -16(%rbp)", "movq\t$0, -8(%rbp)"),
        ("-1", "movq\t$-1, -16(%rbp)", "movq\t$-1, -8(%rbp)"),
        (
            "18446744073709551616",
            "movq\t$0, -16(%rbp)",
            "movq\t$1, -8(%rbp)",
        ),
        (
            "-170141183460469231731687303715884105728",
            "movq\t$0, -16(%rbp)",
            "movabsq\t$-9223372036854775808, %rax\n\tmovq\t%rax, -8(%rbp)",
        ),
        (
            "9223372036854775808",
            "movabsq\t$-9223372036854775808, %rax\n\tmovq\t%rax, -16(%rbp)",
            "movq\t$0, -8(%rbp)",
        ),
    ] {
        let asm = lowered(&format!(
            "func @f() -> i128 {{\n^entry:\n  %r: i128 = const {v} @0\n  ret %r @0\n}}\n"
        ));
        assert_op(&asm, &format!("%r: i128 = const {v}"), &[lo, hi]);
    }
}

#[test]
fn poison_writes_zero_into_both_halves() {
    let line = "%r: i128 = poison";
    let asm = lowered(&format!(
        "func @f() -> i128 {{\n^entry:\n  {line} @0\n  ret %r @0\n}}\n"
    ));
    assert_op(&asm, line, &["movq\t$0, -16(%rbp)", "movq\t$0, -8(%rbp)"]);
}

#[test]
fn an_i128_returns_in_rdx_and_rax() {
    let asm = lowered("func @f(%a: i128) -> i128 {\n^entry:\n  ret %a @0\n}\n");
    let want = "\t# ret %a @0\n\tmovq\t-16(%rbp), %rax\n\tmovq\t-8(%rbp), %rdx\n\tleave\n\tret\n";
    assert!(asm.contains(want), "{asm}");
}

/// Five `i64`s leave one register, so the `i128` is read from the stack,
/// and the `i64` after it from `%r9`. Past a seventh `i64`, an `i128` is
/// read from 16 bytes further up, past a hole.
#[test]
fn parameters_are_read_from_where_the_layout_puts_them() {
    let asm = lowered(
        "func @f(%a: i64, %b: i64, %c: i64, %d: i64, %e: i64, %x: i128, %y: i64) -> i128 {\n^entry:\n  ret %x @0\n}\n",
    );
    let want = "\tmovq\t%r8, -40(%rbp)\n\tmovq\t16(%rbp), %rax\n\tmovq\t%rax, -56(%rbp)\n\
                \tmovq\t24(%rbp), %rax\n\tmovq\t%rax, -48(%rbp)\n\tmovq\t%r9, -64(%rbp)\n";
    assert!(asm.contains(want), "{want}\nnot in\n{asm}");
    let asm = lowered(
        "func @f(%x: i128, %y: i128, %z: i128, %s: i64, %w: i128) -> i128 {\n^entry:\n  ret %w @0\n}\n",
    );
    let want = "\tmovq\t%rdi, -16(%rbp)\n\tmovq\t%rsi, -8(%rbp)\n\tmovq\t%rdx, -32(%rbp)\n\
                \tmovq\t%rcx, -24(%rbp)\n\tmovq\t%r8, -48(%rbp)\n\tmovq\t%r9, -40(%rbp)\n\
                \tmovq\t16(%rbp), %rax\n\tmovq\t%rax, -56(%rbp)\n\tmovq\t32(%rbp), %rax\n\
                \tmovq\t%rax, -72(%rbp)\n\tmovq\t40(%rbp), %rax\n\tmovq\t%rax, -64(%rbp)\n";
    assert!(asm.contains(want), "{want}\nnot in\n{asm}");
}

/// A call pushes an `i128` on the stack high half first, so that its low
/// half is the lower address, and stores the result from `%rax` and `%rdx`.
#[test]
fn a_call_passes_and_returns_both_halves() {
    let asm = lowered(
        "func @g(%a: i64, %b: i64, %c: i64, %d: i64, %e: i64, %x: i128, %y: i64) -> i128 {\n^entry:\n  ret %x @0\n}\n\n\
         func @f(%n: i64, %x: i128) -> i128 {\n^entry:\n  %r: i128 = call @g %n, %n, %n, %n, %n, %x, %n @0\n  ret %r @0\n}\n",
    );
    let want = [
        "\t# %r: i128 = call @g %n, %n, %n, %n, %n, %x, %n @0",
        "\tpushq\t-16(%rbp)",
        "\tpushq\t-24(%rbp)",
        "\tmovq\t-8(%rbp), %rdi",
        "\tmovq\t-8(%rbp), %rsi",
        "\tmovq\t-8(%rbp), %rdx",
        "\tmovq\t-8(%rbp), %rcx",
        "\tmovq\t-8(%rbp), %r8",
        "\tmovq\t-8(%rbp), %r9",
        "\tcall\tg",
        "\taddq\t$16, %rsp",
        "\tmovq\t%rax, -40(%rbp)",
        "\tmovq\t%rdx, -32(%rbp)",
        "",
    ]
    .join("\n");
    assert!(asm.contains(&want), "{want}\nnot in\n{asm}");
}

/// Swapping two `i128` block arguments is two cycles of eightbytes: one for
/// the low halves and one for the high ones, each through `%rcx`.
#[test]
fn a_swap_of_i128_block_arguments_moves_each_half_in_a_cycle() {
    let asm = lowered(
        "func @f(%a: i128, %b: i128, %c: i1) -> i128 {\n^entry:\n  br ^loop(%a, %b) @0\n\
         ^loop(%x: i128, %y: i128):\n  cond_br %c, ^loop(%y, %x), ^done @0\n^done:\n  ret %x @0\n}\n",
    );
    let saves = asm.matches("\tmovq\t-56(%rbp), %rcx\n").count()
        + asm.matches("\tmovq\t-48(%rbp), %rcx\n").count();
    assert_eq!(saves, 2, "{asm}");
    for (x, y) in [("-56", "-72"), ("-48", "-64")] {
        let half = format!(
            "\tmovq\t{x}(%rbp), %rcx\n\tmovq\t{y}(%rbp), %rax\n\tmovq\t%rax, {x}(%rbp)\n\tmovq\t%rcx, {y}(%rbp)\n"
        );
        assert!(asm.contains(&half), "{half}\nnot in\n{asm}");
    }
}
