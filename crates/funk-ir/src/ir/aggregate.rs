//! Aggregates' layouts (`Aggregate` in `lean/Fir/Syntax/Module.lean`,
//! ADR-2026-11-16-1546): an item of the core's kind `aggregate` that names a
//! memory, a size, an alignment and fields, each at an offset, all counted
//! in the units of that memory (ADR-2026-11-09-1550).
//!
//! The text writes one as
//! `aggregate @pair() memory(0) size(16) align(8) field(0, i64) field(8, ptr) {`
//! and `}` on the next line. A repeated field writes its count third:
//! `field(0, i24, 4)`. Every number is at most `2^64 - 1`, so it is a
//! `u64` here, and every other attribute does not decode.

use super::attr::{Attr, Type};
use super::int::Int;

/// A field of an aggregate's layout: its offset, its type, a scalar, and
/// its count when it is a repeated field.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Field {
    /// The field's offset, in units of the layout's memory.
    pub offset: u64,
    /// The type of the field, or of each of its elements.
    pub ty: Type,
    /// The number of elements of a repeated field; `None` for one value.
    pub count: Option<u64>,
}

/// The layout of an aggregate.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Aggregate {
    /// The layout's symbol, without `@`. Any string.
    pub name: String,
    /// The memory the layout describes, by its number.
    pub memory: u64,
    /// The layout's size, in units of its memory.
    pub size: u64,
    /// The layout's alignment, in units of its memory.
    pub align: u64,
    /// The fields, in the order the text writes them.
    pub fields: Vec<Field>,
}

impl Aggregate {
    /// The layout `name` of `size` units of `memory`, aligned to `align`,
    /// with no fields.
    pub fn new(name: impl Into<String>, memory: u64, size: u64, align: u64) -> Aggregate {
        Aggregate {
            name: name.into(),
            memory,
            size,
            align,
            fields: Vec::new(),
        }
    }

    /// The layout with the field `ty` at `offset`, of `count` elements when
    /// it is repeated, after its fields.
    pub fn field(mut self, offset: u64, ty: Type, count: Option<u64>) -> Aggregate {
        self.fields.push(Field { offset, ty, count });
        self
    }

    /// Every type that the layout states: the type of each field
    /// (`Aggregate.types`).
    pub fn types(&self) -> impl Iterator<Item = &Type> {
        self.fields.iter().map(|f| &f.ty)
    }

    /// The layout `name` that the attributes write (`decodeAggregate`):
    /// its memory, size and alignment, then its fields, each checked whole,
    /// its type by `type_ok`, before the next, so the first field that does
    /// not decode is the one reported, as `fs.mapM decodeField` reports it.
    pub fn decode(
        name: impl Into<String>,
        attrs: &[Attr],
        type_ok: impl Fn(&Type) -> bool,
    ) -> Result<Aggregate, AggregateFault> {
        let [m, s, a, fields @ ..] = attrs else {
            return Err(AggregateFault::Header);
        };
        let memory = applied(m, "memory").ok_or(AggregateFault::Memory)?;
        let size = applied(s, "size").ok_or(AggregateFault::Size)?;
        let align = applied(a, "align").ok_or(AggregateFault::Align)?;
        let fields = fields
            .iter()
            .enumerate()
            .map(|(i, f)| {
                decode_field(f)
                    .filter(|f| type_ok(&f.ty))
                    .ok_or(AggregateFault::Field(i))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Aggregate {
            name: name.into(),
            memory,
            size,
            align,
            fields,
        })
    }
}

/// Why an aggregate's attributes do not decode.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AggregateFault {
    /// There are fewer than three attributes.
    Header,
    /// The first is not `memory(N)`, `N` at most `2^64 - 1`.
    Memory,
    /// The second is not `size(S)`.
    Size,
    /// The third is not `align(A)`.
    Align,
    /// The field at this index, from 0, is not `field(O, T)` or
    /// `field(O, T, C)`.
    Field(usize),
}

/// The number of `head(n)`, `n` from 0 to `2^64 - 1`
/// (`Aggregate.decodeNumber`).
fn applied(a: &Attr, head: &str) -> Option<u64> {
    match a {
        Attr::App(h, args) if h == head => match args.as_slice() {
            [Attr::Int(n)] => number(n),
            _ => None,
        },
        _ => None,
    }
}

/// An integer from 0 to `2^64 - 1` (`Aggregate.number`).
fn number(n: &Int) -> Option<u64> {
    n.as_str().parse::<u64>().ok()
}

/// The field that an attribute writes (`Field.decode`): its type is a word,
/// or a word applied to attributes. Whether the type decodes is the
/// registry's question.
fn decode_field(a: &Attr) -> Option<Field> {
    let Attr::App(h, args) = a else {
        return None;
    };
    if h != "field" {
        return None;
    }
    let (o, t, count) = match args.as_slice() {
        [Attr::Int(o), t] => (o, t, None),
        [Attr::Int(o), t, Attr::Int(c)] => (o, t, Some(number(c)?)),
        _ => return None,
    };
    let ty = match t {
        Attr::Word(w) => Type::word(w.clone()),
        Attr::App(w, args) => Type::app(w.clone(), args.clone()),
        _ => return None,
    };
    Some(Field {
        offset: number(o)?,
        ty,
        count,
    })
}

/// `u` rounded up to a multiple of `a`, and 0 when `a` is 0, as in Lean
/// (`roundUp`): the units of one element of a repeated field.
fn round_up(u: u128, a: u128) -> u128 {
    u.checked_next_multiple_of(a).unwrap_or(0)
}

impl Field {
    /// The units that the field takes, where one value of its type takes
    /// `u` units aligned to `a` (`Field.extent`): `u`, or for a repeated
    /// field its count times `u` rounded up to `a`.
    pub(crate) fn extent(&self, u: u128, a: u128) -> u128 {
        match self.count {
            None => u,
            Some(c) => u128::from(c) * round_up(u, a),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_repeated_field_rounds_its_elements_up_to_their_alignment() {
        assert_eq!(round_up(3, 4), 4);
        assert_eq!(round_up(10, 16), 16);
        assert_eq!(round_up(5, 0), 0);
        let f = Field {
            offset: 0,
            ty: Type::word("i24"),
            count: Some(4),
        };
        assert_eq!(f.extent(3, 4), 16);
    }

    #[test]
    fn attributes_decode_as_the_spec_says() {
        let n = |h: &str, v: i128| Attr::App(h.into(), vec![Attr::int(v)]);
        let field = Attr::App("field".into(), vec![Attr::int(8), Attr::word("ptr")]);
        let any = |_: &Type| true;
        let decode = |attrs: &[Attr]| Aggregate::decode("s", attrs, any);
        let a = decode(&[n("memory", 0), n("size", 16), n("align", 8), field]);
        assert_eq!(
            a,
            Ok(Aggregate::new("s", 0, 16, 8).field(8, Type::word("ptr"), None))
        );
        assert_eq!(
            decode(&[n("size", 0), n("memory", 0), n("align", 1)]),
            Err(AggregateFault::Memory)
        );
        assert_eq!(
            decode(&[n("memory", 0), n("size", -1), n("align", 1)]),
            Err(AggregateFault::Size)
        );
        let bad = Attr::App("field".into(), vec![Attr::int(0), Attr::int(5)]);
        assert_eq!(
            decode(&[n("memory", 0), n("size", 0), n("align", 1), bad]),
            Err(AggregateFault::Field(0))
        );
        assert_eq!(decode(&[n("memory", 0)]), Err(AggregateFault::Header));
        // A field whose type does not decode is reported before a later
        // field that is not a field at all.
        let wide = Attr::App("field".into(), vec![Attr::int(0), Attr::word("i0x")]);
        let neg = Attr::App("field".into(), vec![Attr::int(-1), Attr::word("i8")]);
        let typed = |t: &Type| t != &Type::word("i0x");
        assert_eq!(
            Aggregate::decode(
                "s",
                &[n("memory", 0), n("size", 4), n("align", 4), wide, neg],
                typed
            ),
            Err(AggregateFault::Field(0))
        );
    }
}
