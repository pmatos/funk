//! Globals (`Global` in `lean/Fir/Syntax/Module.lean`, ADR-2026-11-09-1546):
//! an item of the core's kind `global` that names a block of units of one
//! memory, with its size, its alignment, its initial units, a `const` flag
//! and its linkage.
//!
//! The text writes one as
//! `global @msg() size(8) align(1) const units(104, 105, 0) {` and `}` on
//! the next line (`lean/Fir/Text/GlobalText.lean`, ADR-2026-11-19-0124):
//! `memory(N)` first when `N` is not 0, `size(S)` and `align(A)`, the words
//! `const` and `export` when they hold, then the pieces of the
//! initializer, `units(U, ...)`, `zeros(N)` and `addr(@s)` or `addr(@s, K)`
//! with `K` not 0. Every number but a unit's is at most `2^64 - 1`, so it is
//! a `u64` here; a unit is any natural number, kept as its spelling.

use super::aggregate::{applied, number};
use super::attr::Attr;
use super::int::Int;

/// A global's linkage: seen by the module alone, or exported.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Linkage {
    /// The default: only the module sees the global.
    Internal,
    /// Written `export`: code that funk did not compile sees it too.
    Exported,
}

/// A piece of a global's initializer, which fills its units in order.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum InitPiece {
    /// Units given one by one, each a natural number.
    Units(Vec<Int>),
    /// This many zero units.
    Zeros(u64),
    /// The address of the global with this symbol, without `@`, plus this
    /// many units.
    Addr(String, u64),
}

/// A global.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Global {
    /// The global's symbol, without `@`. Any string.
    pub name: String,
    /// The memory the global lives in, by its number.
    pub memory: u64,
    /// The global's size, in units of its memory.
    pub size: u64,
    /// The global's alignment, in units of its memory.
    pub align: u64,
    /// Whether the global is constant: writing it is UB.
    pub constant: bool,
    /// The global's linkage.
    pub linkage: Linkage,
    /// The pieces of the initializer, in order.
    pub init: Vec<InitPiece>,
}

impl Global {
    /// The internal, writable global `name` of `size` units of `memory`,
    /// aligned to `align`, with no initializer.
    pub fn new(name: impl Into<String>, memory: u64, size: u64, align: u64) -> Global {
        Global {
            name: name.into(),
            memory,
            size,
            align,
            constant: false,
            linkage: Linkage::Internal,
            init: Vec::new(),
        }
    }

    /// The global `name` that the attributes write (`Global.decodeAttrs`),
    /// or where and why they stop decoding.
    pub fn decode(name: impl Into<String>, attrs: &[Attr]) -> Result<Global, GlobalFault> {
        let (memory, mut i) = match attrs.first() {
            Some(Attr::App(h, _)) if h == "memory" => match applied(&attrs[0], "memory") {
                Some(n) if n != 0 => (n, 1),
                _ => return Err(GlobalFault::Memory),
            },
            _ => (0, 0),
        };
        let (Some(s), Some(a)) = (attrs.get(i), attrs.get(i + 1)) else {
            return Err(GlobalFault::Header);
        };
        let size = applied(s, "size").ok_or(GlobalFault::Size(i))?;
        let align = applied(a, "align").ok_or(GlobalFault::Align(i + 1))?;
        i += 2;
        let mut flag = |w: &str| {
            let hit = matches!(attrs.get(i), Some(Attr::Word(x)) if x == w);
            i += usize::from(hit);
            hit
        };
        let constant = flag("const");
        let linkage = if flag("export") {
            Linkage::Exported
        } else {
            Linkage::Internal
        };
        let init = attrs[i..]
            .iter()
            .enumerate()
            .map(|(k, a)| decode_piece(a).ok_or(GlobalFault::Piece(i + k)))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Global {
            name: name.into(),
            memory,
            size,
            align,
            constant,
            linkage,
            init,
        })
    }
}

/// Why a global's attributes do not decode, with the index of the
/// attribute that does not, as `GlobalFault` gives it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GlobalFault {
    /// There are too few attributes for a size and an alignment.
    Header,
    /// The first is `memory(…)` but not `memory(N)`, `N` from 1 to
    /// `2^64 - 1`.
    Memory,
    /// This one is not `size(S)`.
    Size(usize),
    /// This one is not `align(A)`.
    Align(usize),
    /// This one is not a piece of an initializer.
    Piece(usize),
}

/// The piece that an attribute writes (`InitPiece.decode`).
fn decode_piece(a: &Attr) -> Option<InitPiece> {
    let Attr::App(h, args) = a else {
        return None;
    };
    match (h.as_str(), args.as_slice()) {
        ("units", us) => us
            .iter()
            .map(|u| match u {
                Attr::Int(n) if !n.is_negative() => Some(n.clone()),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()
            .map(InitPiece::Units),
        ("zeros", [Attr::Int(n)]) => number(n).map(InitPiece::Zeros),
        ("addr", [Attr::Sym(s)]) => Some(InitPiece::Addr(s.clone(), 0)),
        ("addr", [Attr::Sym(s), Attr::Int(k)]) => number(k)
            .filter(|&k| k != 0)
            .map(|k| InitPiece::Addr(s.clone(), k)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(h: &str, v: i128) -> Attr {
        Attr::App(h.into(), vec![Attr::int(v)])
    }

    #[test]
    fn attributes_decode_as_the_spec_says() {
        let units = Attr::App("units".into(), vec![Attr::int(1), Attr::int(2)]);
        let addr = Attr::App("addr".into(), vec![Attr::Sym("g".into()), Attr::int(8)]);
        let g = Global::decode(
            "s",
            &[
                n("size", 16),
                n("align", 8),
                Attr::word("const"),
                Attr::word("export"),
                units,
                n("zeros", 6),
                addr,
            ],
        );
        let mut want = Global::new("s", 0, 16, 8);
        want.constant = true;
        want.linkage = Linkage::Exported;
        want.init = vec![
            InitPiece::Units(vec![Int::from(1), Int::from(2)]),
            InitPiece::Zeros(6),
            InitPiece::Addr("g".into(), 8),
        ];
        assert_eq!(g, Ok(want));
        let m = Global::decode("s", &[n("memory", 2), n("size", 1), n("align", 1)]);
        assert_eq!(m, Ok(Global::new("s", 2, 1, 1)));
        assert_eq!(
            Global::decode("s", &[n("memory", 0), n("size", 1), n("align", 1)]),
            Err(GlobalFault::Memory)
        );
        assert_eq!(
            Global::decode("s", &[n("align", 1), n("size", 1)]),
            Err(GlobalFault::Size(0))
        );
        assert_eq!(
            Global::decode("s", &[n("size", 1), n("align", -1)]),
            Err(GlobalFault::Align(1))
        );
        assert_eq!(
            Global::decode("s", &[n("size", 1)]),
            Err(GlobalFault::Header)
        );
        // `export` before `const` leaves `const` as a piece, which it is not.
        assert_eq!(
            Global::decode(
                "s",
                &[
                    n("size", 1),
                    n("align", 1),
                    Attr::word("export"),
                    Attr::word("const")
                ]
            ),
            Err(GlobalFault::Piece(3))
        );
        let zero = Attr::App("addr".into(), vec![Attr::Sym("g".into()), Attr::int(0)]);
        assert_eq!(
            Global::decode("s", &[n("size", 1), n("align", 1), zero]),
            Err(GlobalFault::Piece(2))
        );
        let neg = Attr::App("units".into(), vec![Attr::int(-1)]);
        assert_eq!(
            Global::decode("s", &[n("size", 1), n("align", 1), neg]),
            Err(GlobalFault::Piece(2))
        );
    }
}
