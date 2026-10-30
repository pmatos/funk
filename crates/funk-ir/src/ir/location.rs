//! Locations and the location table (H8, ADR-2026-10-29-2013;
//! `lean/Fir/Syntax/Location.lean`).
//!
//! Every op holds a location reference, a number, and the module's location
//! table gives the location each number stands for. References, lines and
//! columns are below `2^32` (N3), so they are `u32`.

use std::fmt;

/// A location reference: the key of an entry in the location table, written
/// `@N`. References are the producer's: stored and printed as given.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocRef(pub u32);

impl fmt::Display for LocRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "@{}", self.0)
    }
}

/// A location: where an op came from. Every kind but `Unknown` and `Range`
/// is built from other entries of the table, by reference.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Location {
    /// Nothing is known about where the op came from.
    Unknown,
    /// A range of source text, written `"file":l:c to l:c`. Lines count from
    /// 1, columns count UTF-8 bytes from 1, column 0 is an unknown column,
    /// and the end is exclusive.
    Range {
        /// The source file.
        file: String,
        /// The first line.
        start_line: u32,
        /// The first column.
        start_col: u32,
        /// The line of the end.
        end_line: u32,
        /// The column just after the last byte.
        end_col: u32,
    },
    /// A name, such as the source variable an op computes.
    Name(String),
    /// The op came from inlining: its location in the inlined function, and
    /// the location of the call.
    CallSite {
        /// The location in the inlined function.
        callee: LocRef,
        /// The location of the call.
        caller: LocRef,
    },
    /// The op stands for two or more ops.
    Fused(Vec<LocRef>),
    /// A transformation made the op from the op at this location.
    Derived(LocRef),
}

impl Location {
    /// The references this location is built from.
    pub fn refs(&self) -> Vec<LocRef> {
        match self {
            Location::Unknown | Location::Range { .. } | Location::Name(_) => Vec::new(),
            Location::CallSite { callee, caller } => vec![*callee, *caller],
            Location::Fused(locs) => locs.clone(),
            Location::Derived(src) => vec![*src],
        }
    }
}

/// The location table: entries from a reference to a location, kept and
/// printed in the order they are stored.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct LocTable {
    /// The entries, in order.
    pub entries: Vec<(LocRef, Location)>,
}

impl LocTable {
    /// An empty table.
    pub fn new() -> LocTable {
        LocTable::default()
    }

    /// Adds `loc` under the reference after the last one, `@0` for the
    /// first, and returns that reference. Panics if the last reference is
    /// already the largest.
    pub fn push(&mut self, loc: Location) -> LocRef {
        let next = self.entries.last().map_or(0, |(r, _)| {
            r.0.checked_add(1)
                .expect("no location reference comes after @4294967295")
        });
        self.entries.push((LocRef(next), loc));
        LocRef(next)
    }

    /// Adds `loc` under the reference `r`, after the existing entries.
    pub fn insert(&mut self, r: LocRef, loc: Location) -> LocRef {
        self.entries.push((r, loc));
        r
    }

    /// The location that `r` stands for: its first entry.
    pub fn get(&self, r: LocRef) -> Option<&Location> {
        self.entries.iter().find(|(k, _)| *k == r).map(|(_, l)| l)
    }
}
