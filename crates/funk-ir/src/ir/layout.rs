//! A module's data layout (`lean/Fir/Syntax/Layout.lean`): its memories,
//! each with the width of its unit, the width of its pointers, its byte
//! order, its pointers' alignment and whether it is non-integral
//! (ADR-2026-11-12-1821).
//!
//! The text writes the layout on one line after the dialect set:
//! `layout memory(1, unit(16), pointer(32), little, align(4), nonintegral)`.
//! Each entry is `memory(N, unit(U), pointer(P), O)`, then `align(A)` when
//! the entry gives an alignment and `nonintegral` when the memory is
//! non-integral, in that order. Every other attribute does not decode, and
//! neither does a number above [`MemLayout::LIMIT`]. A module with no line
//! has the empty layout: memory 0 alone, with [`MemLayout::DEFAULT`].

use super::attr::{Attr, Type};

/// The order of the units of a value that spans several units of a memory.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ByteOrder {
    /// The least significant unit first, at the lowest offset.
    Little,
    /// The most significant unit first. M1's validation rejects it.
    Big,
}

impl ByteOrder {
    /// The word that writes the byte order.
    pub fn word(self) -> &'static str {
        match self {
            ByteOrder::Little => "little",
            ByteOrder::Big => "big",
        }
    }

    fn decode(w: &str) -> Option<ByteOrder> {
        match w {
            "little" => Some(ByteOrder::Little),
            "big" => Some(ByteOrder::Big),
            _ => None,
        }
    }
}

/// The entry of the data layout for one memory.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MemLayout {
    /// The memory's number, `N` in `ptr<N>`.
    pub mem: u32,
    /// The width of the memory's unit of addressing, in bits.
    pub unit: u32,
    /// The width of the memory's pointers, in bits.
    pub pointer: u32,
    /// The memory's byte order.
    pub order: ByteOrder,
    /// The alignment of the memory's pointers, in units, when the entry
    /// gives one; `None` is their natural alignment.
    pub align: Option<u32>,
    /// Whether the memory is non-integral, as LLVM's `ni:`: its pointers
    /// never become integers.
    pub non_integral: bool,
}

const MEMORY: &str = "memory";
const UNIT: &str = "unit";
const POINTER: &str = "pointer";
const ALIGN: &str = "align";
const NON_INTEGRAL: &str = "nonintegral";

impl MemLayout {
    /// The largest number that an entry gives: a memory, a width or an
    /// alignment, `2^24 - 1`.
    pub const LIMIT: u32 = (1 << 24) - 1;

    /// The default memory's entry when the layout does not declare it.
    pub const DEFAULT: MemLayout = MemLayout {
        mem: 0,
        unit: 8,
        pointer: 64,
        order: ByteOrder::Little,
        align: None,
        non_integral: false,
    };

    /// The units that a pointer of the memory takes: its width over the
    /// unit's, rounded up.
    pub fn pointer_units(&self) -> u32 {
        self.pointer.div_ceil(self.unit.max(1))
    }

    /// The alignment of the memory's pointers, in units: the entry's own,
    /// or the natural one, the least power of two that is at least the
    /// units a pointer takes.
    pub fn alignment(&self) -> u32 {
        self.align
            .unwrap_or_else(|| self.pointer_units().next_power_of_two())
    }

    /// How the entry is written, as a type of the grammar.
    pub fn to_type(&self) -> Type {
        let num = |n: u32| Attr::int(i128::from(n));
        let mut args = vec![
            num(self.mem),
            Attr::App(UNIT.into(), vec![num(self.unit)]),
            Attr::App(POINTER.into(), vec![num(self.pointer)]),
            Attr::word(self.order.word()),
        ];
        if let Some(a) = self.align {
            args.push(Attr::App(ALIGN.into(), vec![num(a)]));
        }
        if self.non_integral {
            args.push(Attr::word(NON_INTEGRAL));
        }
        Type::app(MEMORY, args)
    }

    /// The entry that `ty` writes, if it writes one (`MemLayout.decode`).
    pub fn decode(ty: &Type) -> Option<MemLayout> {
        if ty.name != MEMORY {
            return None;
        }
        let [Attr::Int(n), unit, pointer, Attr::Word(o), rest @ ..] = ty.args.as_deref()? else {
            return None;
        };
        let (align, non_integral) = match rest {
            [] => (None, false),
            [Attr::Word(w)] if w == NON_INTEGRAL => (None, true),
            [a] => (Some(applied(a, ALIGN)?), false),
            [a, Attr::Word(w)] if w == NON_INTEGRAL => (Some(applied(a, ALIGN)?), true),
            _ => return None,
        };
        Some(MemLayout {
            mem: number(n)?,
            unit: applied(unit, UNIT)?,
            pointer: applied(pointer, POINTER)?,
            order: ByteOrder::decode(o)?,
            align,
            non_integral,
        })
    }
}

/// The number that an integer of an entry writes: one from 0 to the limit.
fn number(n: &super::Int) -> Option<u32> {
    n.as_str()
        .parse::<u32>()
        .ok()
        .filter(|&v| v <= MemLayout::LIMIT)
}

/// The number of `head(n)`.
fn applied(a: &Attr, head: &str) -> Option<u32> {
    match a {
        Attr::App(h, args) if h == head => match args.as_slice() {
            [Attr::Int(n)] => number(n),
            _ => None,
        },
        _ => None,
    }
}

/// The entry of memory `n` in `layout`: the first it declares for `n`, or
/// the default for memory 0 (`DataLayout.memory?`).
pub fn memory(layout: &[MemLayout], n: u32) -> Option<MemLayout> {
    layout
        .iter()
        .find(|e| e.mem == n)
        .copied()
        .or((n == 0).then_some(MemLayout::DEFAULT))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(align: Option<u32>, non_integral: bool) -> MemLayout {
        MemLayout {
            mem: 1,
            unit: 16,
            pointer: 32,
            order: ByteOrder::Big,
            align,
            non_integral,
        }
    }

    #[test]
    fn each_entry_reads_back() {
        for e in [
            MemLayout::DEFAULT,
            entry(None, false),
            entry(Some(4), false),
            entry(None, true),
            entry(Some(4), true),
        ] {
            assert_eq!(MemLayout::decode(&e.to_type()), Some(e));
        }
        assert_eq!(
            entry(Some(4), true).to_type().to_string(),
            "memory(1, unit(16), pointer(32), big, align(4), nonintegral)"
        );
    }

    #[test]
    fn other_attributes_are_no_entry() {
        let bad = |args: Vec<Attr>| MemLayout::decode(&Type::app(MEMORY, args));
        let base = || {
            vec![
                Attr::int(1),
                Attr::App(UNIT.into(), vec![Attr::int(8)]),
                Attr::App(POINTER.into(), vec![Attr::int(64)]),
                Attr::word("little"),
            ]
        };
        assert!(bad(base()).is_some());
        let mut a = base();
        a.push(Attr::word(NON_INTEGRAL));
        a.push(Attr::App(ALIGN.into(), vec![Attr::int(8)]));
        assert_eq!(bad(a), None, "align after nonintegral");
        let mut a = base();
        a[3] = Attr::word("middle");
        assert_eq!(bad(a), None);
        let mut a = base();
        a[0] = Attr::int(-1);
        assert_eq!(bad(a), None);
        let mut a = base();
        a[0] = Attr::int(i128::from(MemLayout::LIMIT) + 1);
        assert_eq!(bad(a), None);
        let mut a = base();
        a.swap(1, 2);
        assert_eq!(bad(a), None);
        assert_eq!(bad(base()[..3].to_vec()), None);
        assert_eq!(MemLayout::decode(&Type::word(MEMORY)), None);
    }

    #[test]
    fn the_default_memory_is_in_every_layout() {
        assert_eq!(memory(&[], 0), Some(MemLayout::DEFAULT));
        assert_eq!(memory(&[], 1), None);
        assert_eq!(memory(&[entry(None, false)], 1), Some(entry(None, false)));
        assert_eq!(MemLayout::DEFAULT.pointer_units(), 8);
        assert_eq!(MemLayout::DEFAULT.alignment(), 8);
        assert_eq!(entry(None, false).alignment(), 2);
    }
}
