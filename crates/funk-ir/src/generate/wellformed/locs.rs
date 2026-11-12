//! Location tables that validation rejects but the text writes and reads
//! back (#146).
//!
//! A valid table has entries in increasing order of reference, each built
//! only from entries before it, with well-formed ranges and fused locations
//! of two or more references (`LocTable.Valid` in
//! `lean/Fir/Validation/LocTable.lean`). A well-formed one needs only that its
//! numbers are below `2^32`, which every `u32` is.

use super::super::{Rng, range, string};
use crate::ir::{LocRef, LocTable, Location};

/// A reference after the table's last one, or any reference when none is.
fn next_key(rng: &mut Rng, t: &LocTable) -> LocRef {
    let last = t
        .entries
        .last()
        .map_or(Some(0), |(r, _)| r.0.checked_add(1 + rng.below(3) as u32));
    LocRef(last.unwrap_or_else(|| rng.next_u64() as u32))
}

/// A reference in the table, or any reference when it has none.
fn some_key(rng: &mut Rng, t: &LocTable) -> LocRef {
    if t.entries.is_empty() {
        LocRef(rng.next_u64() as u32)
    } else {
        rng.pick(&t.entries).0
    }
}

/// Adds `fused()` or `fused(@k)`: a fused location of fewer than two
/// references.
pub(super) fn add_short_fused(rng: &mut Rng, t: &mut LocTable) {
    let refs = if rng.one_in(2) {
        Vec::new()
    } else {
        vec![some_key(rng, t)]
    };
    let key = next_key(rng, t);
    t.insert(key, Location::Fused(refs));
}

/// A source range that is not well formed: one that starts at line 0, ends
/// on a line before its start, or ends on its line at a column before its
/// start.
fn bad_range(rng: &mut Rng) -> Location {
    let Location::Range {
        file,
        start_line,
        start_col,
        end_line,
        end_col,
    } = range(rng)
    else {
        unreachable!("range gives a range")
    };
    let line = start_line.max(2);
    let (start_line, start_col, end_line, end_col) = match rng.below(3) {
        0 => (0, start_col, end_line, end_col),
        1 => (
            line,
            start_col,
            line - 1 - rng.below(u64::from(line - 1)) as u32,
            end_col,
        ),
        _ => (start_line, start_col.max(2), start_line, 1),
    };
    Location::Range {
        file,
        start_line,
        start_col,
        end_line,
        end_col,
    }
}

/// Breaks the table in one to three ways: two entries out of order, a
/// reference given twice, an entry that refers to itself, to a later one or
/// to none, a range that is not well formed, or an entry gone, which leaves
/// the ops that refer to it with no location.
pub(super) fn break_table(rng: &mut Rng, t: &mut LocTable) {
    for _ in 0..1 + rng.below(3) {
        let n = t.entries.len();
        match rng.below(5) {
            0 if n >= 2 => {
                let i = rng.below(n as u64 - 1) as usize;
                let j = i + 1 + rng.below((n - i - 1) as u64) as usize;
                t.entries.swap(i, j);
            }
            1 if n >= 1 => {
                let key = some_key(rng, t);
                let loc = if rng.one_in(2) {
                    Location::Unknown
                } else {
                    Location::Name(string(rng))
                };
                let at = rng.below(n as u64 + 1) as usize;
                t.entries.insert(at, (key, loc));
            }
            2 => {
                let key = next_key(rng, t);
                let later = LocRef(key.0.saturating_add(1 + rng.below(5) as u32));
                let loc = match rng.below(3) {
                    0 => Location::Derived(key),
                    1 => Location::CallSite {
                        callee: later,
                        caller: some_key(rng, t),
                    },
                    _ => Location::Fused(vec![some_key(rng, t), later, key]),
                };
                t.insert(key, loc);
            }
            3 => {
                let key = next_key(rng, t);
                t.insert(key, bad_range(rng));
            }
            _ if n >= 1 => {
                t.entries.remove(rng.below(n as u64) as usize);
            }
            _ => {
                let key = next_key(rng, t);
                t.insert(key, Location::Derived(LocRef(rng.next_u64() as u32)));
            }
        }
    }
}
