//! The canonical printer (`lean/Fir/Text/Print.lean`). It is the formatter:
//! `funk fmt` prints a module with it, and it writes every value name,
//! attribute and location as stored, renumbering nothing (P3).
//!
//! The layout: single spaces between tokens, a space after each comma and
//! after the colon of a definition; blocks at the indentation of their
//! function or op, their ops two spaces deeper; one op per line, ending with
//! its location reference; one empty line after each item; then the location
//! table; and a line feed at the end of every line.
//!
//! Attributes and regions nest to any depth, so they are printed from the
//! steps of a walk, not by recursive calls (ADR-2026-10-30-1333).

use std::fmt::{self, Display, Write};

use super::chars::{print_symbol, quote};
use crate::ir::tree::{Step, walk};
use crate::ir::{Attr, Block, Def, Func, Item, LocTable, Location, Module, Op, Part, Succ, Type};

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

fn indent(out: &mut String, n: usize) {
    out.extend(std::iter::repeat_n(' ', n));
}

/// A block or an op at indentation `n`, with the blocks and ops of its
/// regions at any depth: each region's blocks two spaces deeper than its op,
/// and each block's ops two spaces deeper than the block.
fn write_part(out: &mut String, root: Part<'_>, mut n: usize) {
    for step in walk(root) {
        match step {
            Step::Enter(Part::Op(op)) => write_op_head(out, n, op),
            Step::Enter(Part::Region(_)) => {
                out.push_str(" {\n");
                n += 2;
            }
            Step::Enter(Part::Block(b)) => {
                write_block_head(out, n, b);
                n += 2;
            }
            Step::Leave(Part::Op(op)) => {
                let _ = writeln!(out, " {}", op.loc);
            }
            Step::Leave(Part::Region(_)) => {
                n -= 2;
                indent(out, n);
                out.push('}');
            }
            Step::Leave(Part::Block(_)) => n -= 2,
        }
    }
}

/// An op up to its regions, at indentation `n`.
fn write_op_head(out: &mut String, n: usize, op: &Op) {
    indent(out, n);
    if !op.results.is_empty() {
        let _ = write!(out, "{} = ", Commas(&op.results));
    }
    out.push_str(&op.name);
    for a in &op.attrs {
        let _ = write!(out, " {a}");
    }
    let mut sep = " ";
    for x in &op.operands {
        let _ = write!(out, "{sep}%{x}");
        sep = ", ";
    }
    for s in &op.succs {
        let _ = write!(out, "{sep}{s}");
        sep = ", ";
    }
}

/// A block's label and arguments, at indentation `n`.
fn write_block_head(out: &mut String, n: usize, b: &Block) {
    indent(out, n);
    out.push('^');
    out.push_str(&b.label);
    if !b.params.is_empty() {
        let _ = write!(out, "({})", Commas(&b.params));
    }
    out.push_str(":\n");
}

/// A function: an item of kind `func`, with no attributes.
fn write_func(out: &mut String, f: &Func) {
    let _ = write!(out, "func {}({})", print_symbol(&f.name), Commas(&f.params));
    if !f.results.is_empty() {
        let _ = write!(out, " -> {}", Commas(&f.results));
    }
    out.push_str(" {\n");
    for b in &f.body.blocks {
        write_part(out, Part::Block(b), 0);
    }
    out.push_str("}\n");
}

fn write_locs(out: &mut String, t: &LocTable) {
    out.push_str("locs {\n");
    for (r, l) in &t.entries {
        let _ = writeln!(out, "  {r} = {l}");
    }
    out.push_str("}\n");
}

/// The canonical text of a module (`Module.print`).
pub fn print(m: &Module) -> String {
    let mut out = String::new();
    for item in &m.items {
        match item {
            Item::Func(f) => write_func(&mut out, f),
        }
        out.push('\n');
    }
    write_locs(&mut out, &m.locs);
    out
}

/// The canonical text of one op at indentation `n`, with its line feed.
pub fn print_op(op: &Op, n: usize) -> String {
    let mut out = String::new();
    write_part(&mut out, Part::Op(op), n);
    out
}

/// The canonical text of one function, with its line feed.
pub fn print_func(f: &Func) -> String {
    let mut out = String::new();
    write_func(&mut out, f);
    out
}
