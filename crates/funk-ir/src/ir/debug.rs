//! `Debug` for trees of any depth, in the text that `#[derive(Debug)]`
//! writes (ADR-2026-10-30-1333).
//!
//! A derived `Debug` recurses once per level, and its `{:#?}` form indents
//! a nested value by wrapping the formatter. [`DebugTree`] writes the same
//! text from the steps of a walk instead: it keeps the open brackets on a
//! stack and indents by hand, so its native stack does not grow with depth.

use std::fmt::{self, Debug, Formatter, Write};

/// A kind of bracket that `#[derive(Debug)]` writes.
#[derive(Clone, Copy)]
pub(crate) enum Bracket {
    /// `Name { field: value }`.
    Struct,
    /// `Name(value)`.
    Tuple,
    /// `[value]`.
    List,
}

/// Writes `Debug` text bracket by bracket.
pub(crate) struct DebugTree<'a, 'f> {
    f: &'a mut Formatter<'f>,
    pretty: bool,
    /// The open brackets, outermost first, and whether each holds a value.
    open: Vec<(Bracket, bool)>,
}

impl<'a, 'f> DebugTree<'a, 'f> {
    /// Writes to `f`, in the `{:#?}` form when `f` asks for it.
    pub(crate) fn new(f: &'a mut Formatter<'f>) -> DebugTree<'a, 'f> {
        let pretty = f.alternate();
        DebugTree {
            f,
            pretty,
            open: Vec::new(),
        }
    }

    /// Opens a bracket as the next value: `head {`, `head(` or `[`, after
    /// `name: ` when the value is a field.
    pub(crate) fn open(&mut self, name: Option<&str>, head: &str, b: Bracket) -> fmt::Result {
        self.begin(name)?;
        self.f.write_str(head)?;
        self.f.write_str(match (b, self.pretty) {
            (Bracket::Struct, false) => " { ",
            (Bracket::Struct, true) => " {",
            (Bracket::Tuple, _) => "(",
            (Bracket::List, _) => "[",
        })?;
        self.open.push((b, false));
        Ok(())
    }

    /// Writes `value` with its own `Debug` as the next value, after
    /// `name: ` when it is a field. The `{:#?}` form writes it through an
    /// indenting writer, which keeps only the alternate flag, so `value`
    /// must print the same under every other flag: it holds no numbers.
    pub(crate) fn value(&mut self, name: Option<&str>, value: &dyn Debug) -> fmt::Result {
        self.begin(name)?;
        if self.pretty {
            let depth = self.open.len();
            write!(Indented { f: self.f, depth }, "{value:#?}")?;
        } else {
            value.fmt(self.f)?;
        }
        self.end()
    }

    /// Writes `value`, whose `Debug` is one line in every form, such as a
    /// number's, as the next value, with all the formatter's flags, such as
    /// `{:#x?}` and widths.
    pub(crate) fn leaf(&mut self, name: Option<&str>, value: &dyn Debug) -> fmt::Result {
        self.begin(name)?;
        value.fmt(self.f)?;
        self.end()
    }

    /// Closes the innermost open bracket.
    pub(crate) fn close(&mut self) -> fmt::Result {
        let (b, full) = self.open.pop().expect("a bracket is open");
        if self.pretty && full {
            self.f.write_char('\n')?;
            indent(self.f, self.open.len())?;
        }
        self.f.write_str(match (b, self.pretty) {
            (Bracket::Struct, false) => " }",
            (Bracket::Struct, true) => "}",
            (Bracket::Tuple, _) => ")",
            (Bracket::List, _) => "]",
        })?;
        self.end()
    }

    /// Starts a value in the innermost open bracket: after a comma, or on a
    /// line of its own in the `{:#?}` form.
    fn begin(&mut self, name: Option<&str>) -> fmt::Result {
        let depth = self.open.len();
        if let Some((_, full)) = self.open.last_mut() {
            let first = !*full;
            *full = true;
            if self.pretty {
                self.f.write_char('\n')?;
                indent(self.f, depth)?;
            } else if !first {
                self.f.write_str(", ")?;
            }
        }
        match name {
            Some(name) => write!(self.f, "{name}: "),
            None => Ok(()),
        }
    }

    /// Ends a value: the `{:#?}` form ends each value in a bracket with a
    /// comma.
    fn end(&mut self) -> fmt::Result {
        if self.pretty && !self.open.is_empty() {
            self.f.write_char(',')?;
        }
        Ok(())
    }
}

fn indent(f: &mut Formatter<'_>, depth: usize) -> fmt::Result {
    (0..depth).try_for_each(|_| f.write_str("    "))
}

/// Indents every line after the first by `depth` levels, as `{:#?}` does
/// to a value nested that deep.
struct Indented<'a, 'f> {
    f: &'a mut Formatter<'f>,
    depth: usize,
}

impl Write for Indented<'_, '_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let mut lines = s.split('\n');
        if let Some(first) = lines.next() {
            self.f.write_str(first)?;
        }
        for line in lines {
            self.f.write_char('\n')?;
            indent(self.f, self.depth)?;
            self.f.write_str(line)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::ir::{Attr, Block, Def, Int, LocRef, Op, Region, Type};

    /// The IR's recursive types as `#[derive(Debug)]` writes them. Only
    /// their `Debug` reads their fields.
    #[allow(dead_code)]
    mod derived {
        use crate::ir::{Def, Int, LocRef, Succ};

        #[derive(Debug)]
        pub enum Attr {
            Word(String),
            Int(Int),
            Str(String),
            Sym(String),
            App(String, Vec<Attr>),
        }

        #[derive(Debug)]
        pub struct Region {
            pub blocks: Vec<Block>,
        }

        #[derive(Debug)]
        pub struct Block {
            pub label: String,
            pub params: Vec<Def>,
            pub ops: Vec<Op>,
        }

        #[derive(Debug)]
        pub struct Op {
            pub results: Vec<Def>,
            pub name: String,
            pub attrs: Vec<crate::ir::Attr>,
            pub operands: Vec<String>,
            pub succs: Vec<Succ>,
            pub regions: Vec<Region>,
            pub loc: LocRef,
        }
    }

    fn attr(a: &Attr) -> derived::Attr {
        match a {
            Attr::Word(w) => derived::Attr::Word(w.clone()),
            Attr::Int(i) => derived::Attr::Int(i.clone()),
            Attr::Str(s) => derived::Attr::Str(s.clone()),
            Attr::Sym(s) => derived::Attr::Sym(s.clone()),
            Attr::App(h, args) => derived::Attr::App(h.clone(), args.iter().map(attr).collect()),
        }
    }

    fn region(r: &Region) -> derived::Region {
        derived::Region {
            blocks: r.blocks.iter().map(block).collect(),
        }
    }

    fn block(b: &Block) -> derived::Block {
        derived::Block {
            label: b.label.clone(),
            params: b.params.clone(),
            ops: b.ops.iter().map(op).collect(),
        }
    }

    fn op(o: &Op) -> derived::Op {
        derived::Op {
            results: o.results.clone(),
            name: o.name.clone(),
            attrs: o.attrs.clone(),
            operands: o.operands.clone(),
            succs: o.succs.clone(),
            regions: o.regions.iter().map(region).collect(),
            loc: o.loc,
        }
    }

    fn same_debug(ours: &impl std::fmt::Debug, derived: &impl std::fmt::Debug) {
        assert_eq!(format!("{ours:?}"), format!("{derived:?}"));
        assert_eq!(format!("{ours:#?}"), format!("{derived:#?}"));
        assert_eq!(format!("{ours:x?}"), format!("{derived:x?}"));
        assert_eq!(format!("{ours:#x?}"), format!("{derived:#x?}"));
        assert_eq!(format!("{ours:#X?}"), format!("{derived:#X?}"));
        assert_eq!(format!("{ours:5?}"), format!("{derived:5?}"));
        assert_eq!(format!("{ours:#5?}"), format!("{derived:#5?}"));
        assert_eq!(format!("{ours:<+#06x?}"), format!("{derived:<+#06x?}"));
    }

    #[test]
    fn attributes_debug_as_derive_writes_them() {
        let a = Attr::App(
            "vec".into(),
            vec![
                Attr::Int(Int::from(-4)),
                Attr::word("i32"),
                Attr::App("h".into(), vec![]),
                Attr::Str("a\nb".into()),
                Attr::Sym("s".into()),
                Attr::App(
                    "g".into(),
                    vec![Attr::App("k".into(), vec![Attr::word("x")])],
                ),
            ],
        );
        same_debug(&a, &attr(&a));
        same_debug(&Attr::word("w"), &attr(&Attr::word("w")));
    }

    #[test]
    fn regions_debug_as_derive_writes_them() {
        let ty = Type::app("t", vec![Attr::App("h".into(), vec![Attr::int(1)])]);
        let inner = Region::new(vec![
            Block::new("in").op(Op::new("toy.leaf", LocRef(26)).attr(Attr::word("w"))),
        ]);
        let outer = Op::new("toy.wrap", LocRef(10))
            .result("r", ty.clone())
            .attr(Attr::App("f".into(), vec![]))
            .operand("a")
            .succ("next", &["a"])
            .region(inner)
            .region(Region::default());
        let r = Region::new(vec![
            Block::new("entry")
                .param("a", ty)
                .op(outer)
                .op(Op::new("ret", LocRef(0))),
            Block::new("empty"),
        ]);
        same_debug(&r, &region(&r));
        same_debug(&r.blocks[0].ops[0], &op(&r.blocks[0].ops[0]));
        same_debug(&Region::default(), &region(&Region::default()));
        let d = Def::new("x", Type::word("i8"));
        same_debug(
            &Block::new("b").param("x", d.ty.clone()),
            &block(&Block::new("b").param("x", d.ty)),
        );
    }
}
