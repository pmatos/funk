//! The location table (`LocTable.Valid` in `lean/Fir/Validation/Rules.lean`).
//!
//! Each entry has a distinct reference, in increasing order, so one table has
//! one spelling. A location built from others refers only to entries before
//! it. A fused location fuses at least two. A source range starts at line 1
//! or later and does not end before it starts. Every reference, line and
//! column is below `2^32`: the IR holds them as `u32`, so no table can break
//! that rule.

use std::collections::HashSet;

use crate::ir::{LocTable, Location};

/// The broken rules of the table.
pub(super) fn check(t: &LocTable) -> Vec<String> {
    let mut out = Vec::new();
    let keys: HashSet<_> = t.entries.iter().map(|(r, _)| *r).collect();
    for pair in t.entries.windows(2) {
        let (a, b) = (pair[0].0, pair[1].0);
        if a >= b {
            out.push(format!(
                "location table: {b} comes after {a}: references are unique and in increasing order"
            ));
        }
    }
    for (r, loc) in &t.entries {
        if let Some(why) = malformed(loc) {
            out.push(format!("location table: {r} = {loc}: {why}"));
        }
        for x in loc.refs() {
            if !keys.contains(&x) {
                out.push(format!(
                    "location table: {r} refers to {x}, which the table does not hold"
                ));
            } else if x >= *r {
                out.push(format!(
                    "location table: {r} refers to {x}, which does not come before it"
                ));
            }
        }
    }
    out
}

/// Why a location is not well formed (`Location.WellFormed`).
fn malformed(loc: &Location) -> Option<&'static str> {
    match loc {
        Location::Range {
            start_line,
            start_col,
            end_line,
            end_col,
            ..
        } => {
            if *start_line < 1 {
                Some("a range starts at line 1 or later")
            } else if start_line > end_line
                || (start_line == end_line
                    && *start_col != 0
                    && *end_col != 0
                    && start_col > end_col)
            {
                Some("a range does not end before it starts")
            } else {
                None
            }
        }
        Location::Fused(locs) if locs.len() < 2 => Some("a fused location fuses at least two"),
        _ => None,
    }
}
