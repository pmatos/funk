//! The canonical printer (`lean/Fir/Text/Print.lean`). It is the formatter:
//! `funk fmt` prints a module with it, and it writes every value name,
//! attribute and location as stored, renumbering nothing (P3).
//!
//! The layout: single spaces between tokens, a space after each comma and
//! after the colon of a definition; blocks at the indentation of their
//! function or op, their ops two spaces deeper; one op per line, ending with
//! its location reference; a nested module's body two spaces deeper than its
//! `module` line; one empty line after each item; then the location table;
//! and a line feed at the end of every line.
//!
//! Attributes and regions nest to any depth, so they are printed from the
//! steps of a walk, not by recursive calls
//! (`docs/decisions/rust-ir-and-tools.md#nesting`).

use std::fmt::{self, Display, Write};

use super::chars::{print_symbol, quote};
use crate::ir::tree::{Step, walk};
use crate::ir::{
    Attr, Block, Def, DialectItem, Func, Item, LocTable, Location, Module, Op, Part, Succ, Type,
};

impl Display for Attr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Whether the next attribute is the first of its list.
        let mut first = true;
        for step in walk(self) {
            match step {
                Step::Enter(a) => {
                    if !first {
                        f.write_str(", ")?;
                    }
                    match a {
                        Attr::Word(w) => f.write_str(w)?,
                        Attr::Int(i) => write!(f, "{i}")?,
                        Attr::Str(s) => f.write_str(&quote(s))?,
                        Attr::Sym(s) => f.write_str(&print_symbol(s))?,
                        Attr::Float(s) => f.write_str(s)?,
                        Attr::App(h, _) => write!(f, "{h}(")?,
                    }
                    first = matches!(a, Attr::App(..));
                }
                Step::Leave(a) => {
                    if let Attr::App(..) = a {
                        f.write_str(")")?;
                    }
                    first = false;
                }
            }
        }
        Ok(())
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.args {
            None => f.write_str(&self.name),
            Some(args) => write!(f, "{}({})", self.name, Commas(args)),
        }
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Location::Unknown => f.write_str("unknown"),
            Location::Range {
                file,
                start_line,
                start_col,
                end_line,
                end_col,
            } => {
                write!(
                    f,
                    "{}:{start_line}:{start_col} to {end_line}:{end_col}",
                    quote(file)
                )
            }
            Location::Name(n) => write!(f, "name({})", quote(n)),
            Location::CallSite { callee, caller } => write!(f, "callsite({callee} at {caller})"),
            Location::Fused(locs) => write!(f, "fused({})", Commas(locs)),
            Location::Derived(src) => write!(f, "derived({src})"),
        }
    }
}

impl Display for Def {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "%{}: {}", self.name, self.ty)
    }
}

impl Display for Succ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "^{}", self.label)?;
        for (i, a) in self.args.iter().enumerate() {
            write!(f, "{}%{a}", if i == 0 { "(" } else { ", " })?;
        }
        if !self.args.is_empty() {
            f.write_str(")")?;
        }
        Ok(())
    }
}

/// Items separated by `, `.
pub(crate) struct Commas<'a, T>(pub(crate) &'a [T]);

impl<T: Display> Display for Commas<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, x) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{x}")?;
        }
        Ok(())
    }
}

/// Spaces for indentation, written in chunks of at most this many.
const SPACES: &str = "                                                                ";

fn indent(out: &mut impl Write, mut n: usize) -> fmt::Result {
    while n > 0 {
        let k = n.min(SPACES.len());
        out.write_str(&SPACES[..k])?;
        n -= k;
    }
    Ok(())
}

/// A block or an op at indentation `n`, with the blocks and ops of its
/// regions at any depth: each region's blocks two spaces deeper than its op,
/// and each block's ops two spaces deeper than the block.
fn write_part(out: &mut impl Write, root: Part<'_>, mut n: usize) -> fmt::Result {
    for step in walk(root) {
        match step {
            Step::Enter(Part::Op(op)) => write_op_head(out, n, op)?,
            Step::Enter(Part::Region(r)) => {
                out.write_str(" {")?;
                if let Some(kind) = &r.kind {
                    write!(out, " {kind}")?;
                }
                out.write_char('\n')?;
                n += 2;
            }
            Step::Enter(Part::Block(b)) => {
                write_block_head(out, n, b)?;
                n += 2;
            }
            Step::Leave(Part::Op(op)) => writeln!(out, " {}", op.loc)?,
            Step::Leave(Part::Region(_)) => {
                n -= 2;
                indent(out, n)?;
                out.write_char('}')?;
            }
            Step::Leave(Part::Block(_)) => n -= 2,
        }
    }
    Ok(())
}

/// An op up to its regions, at indentation `n`.
fn write_op_head(out: &mut impl Write, n: usize, op: &Op) -> fmt::Result {
    indent(out, n)?;
    if !op.results.is_empty() {
        write!(out, "{} = ", Commas(&op.results))?;
    }
    out.write_str(&op.name)?;
    for a in &op.attrs {
        write!(out, " {a}")?;
    }
    let mut sep = " ";
    for x in &op.operands {
        write!(out, "{sep}%{x}")?;
        sep = ", ";
    }
    for s in &op.succs {
        write!(out, "{sep}{s}")?;
        sep = ", ";
    }
    Ok(())
}

/// A block's label and arguments, at indentation `n`.
fn write_block_head(out: &mut impl Write, n: usize, b: &Block) -> fmt::Result {
    indent(out, n)?;
    out.write_char('^')?;
    out.write_str(&b.label)?;
    if !b.params.is_empty() {
        write!(out, "({})", Commas(&b.params))?;
    }
    out.write_str(":\n")
}

/// A function at indentation `n`: an item of kind `func`, with no
/// attributes. Its header, labels and `}` are at `n`, its ops two spaces
/// deeper.
fn write_func(out: &mut impl Write, f: &Func, n: usize) -> fmt::Result {
    write_header(out, "func", &f.name, &f.params, &f.results, n)?;
    out.write_str(" {\n")?;
    for b in &f.body.blocks {
        write_part(out, Part::Block(b), n)?;
    }
    indent(out, n)?;
    out.write_str("}\n")
}

/// The header of an item at indentation `n`, as the one production of an
/// item writes it: its kind, its symbol, its parameters and, when it has
/// any, its results after ` -> `.
fn write_header(
    out: &mut impl Write,
    kind: &str,
    name: &str,
    params: &[Def],
    results: &[Type],
    n: usize,
) -> fmt::Result {
    indent(out, n)?;
    write!(out, "{kind} {}({})", print_symbol(name), Commas(params))?;
    if !results.is_empty() {
        write!(out, " -> {}", Commas(results))?;
    }
    Ok(())
}

/// An item of a dialect's kind at indentation `n`, with its line feed
/// (`DialectItem.print`): its header as a function's, with its kind in
/// place of `func`, each attribute after a space, then its empty body, whose
/// `}` is on the next line, at `n`.
fn write_dialect_item(out: &mut impl Write, i: &DialectItem, n: usize) -> fmt::Result {
    write_header(out, &i.kind, &i.name, &i.params, &i.results, n)?;
    for a in &i.attrs {
        write!(out, " {a}")?;
    }
    out.write_str(" {\n")?;
    indent(out, n)?;
    out.write_str("}\n")
}

/// A dialect set at indentation `n`, then an empty line, or nothing when it
/// names no dialect.
fn write_dialects(out: &mut impl Write, names: &[String], n: usize) -> fmt::Result {
    if names.is_empty() {
        return Ok(());
    }
    indent(out, n)?;
    writeln!(out, "dialects {}\n", Commas(names))
}

/// Items at indentation `n`, each followed by an empty line. A nested
/// module's body is two spaces deeper than its `module` line, and its `}` at
/// that line's indentation (ADR-2026-11-10-1510). Modules nest to any depth,
/// so the lists of items that enclose the one being written wait on a stack.
fn write_items(out: &mut impl Write, items: &[Item], n: usize) -> fmt::Result {
    let mut open = vec![(items.iter(), n)];
    while let Some((rest, n)) = open.last_mut() {
        let n = *n;
        match rest.next() {
            Some(Item::Func(f)) => {
                write_func(out, f, n)?;
                out.write_char('\n')?;
            }
            Some(Item::Dialect(i)) => {
                write_dialect_item(out, i, n)?;
                out.write_char('\n')?;
            }
            Some(Item::Module(m)) => {
                indent(out, n)?;
                writeln!(out, "module {}() {{", print_symbol(&m.name))?;
                write_dialects(out, &m.dialects, n + 2)?;
                open.push((m.items.iter(), n + 2));
            }
            None => {
                open.pop();
                if let Some((_, outer)) = open.last() {
                    indent(out, *outer)?;
                    out.write_str("}\n\n")?;
                }
            }
        }
    }
    Ok(())
}

fn write_locs(out: &mut impl Write, t: &LocTable) -> fmt::Result {
    out.write_str("locs {\n")?;
    for (r, l) in &t.entries {
        writeln!(out, "  {r} = {l}")?;
    }
    out.write_str("}\n")
}

/// Writes the canonical text of a module (`Module.print`) to `out`, piece
/// by piece, so the text is never held whole. It stops at the first error
/// of `out`, which a sink may return to end the text early.
pub fn write_module(out: &mut impl Write, m: &Module) -> fmt::Result {
    write_dialects(out, &m.dialects, 0)?;
    write_items(out, &m.items, 0)?;
    write_locs(out, &m.locs)
}

/// Runs `write` on a new `String`, which never fails to take a write.
fn to_string(write: impl FnOnce(&mut String) -> fmt::Result) -> String {
    let mut out = String::new();
    write(&mut out).expect("a String takes every write");
    out
}

/// The canonical text of a module (`Module.print`).
pub fn print(m: &Module) -> String {
    to_string(|out| write_module(out, m))
}

/// The canonical text of one op at indentation `n`, with its line feed.
pub fn print_op(op: &Op, n: usize) -> String {
    to_string(|out| write_part(out, Part::Op(op), n))
}

/// The canonical text of one function, with its line feed.
pub fn print_func(f: &Func) -> String {
    to_string(|out| write_func(out, f, 0))
}
