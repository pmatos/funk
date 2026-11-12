//! What the fuzz targets of `fuzz/` and the property tests check of a text
//! (#165, docs/decisions/testing-and-harness-generated.md#fuzzing).

use crate::text::parse_bytes;
use crate::{Module, Registry, parse, print, verify};

/// Parses `data`, and returns the module if it parses, once it has checked
/// that the module round-trips. A panic here is a bug.
pub fn parse_round_trips(data: &[u8], reg: &Registry) -> Option<Module> {
    let m = parse_bytes(data, reg).ok()?;
    let printed = print(&m);
    let back = parse(&printed, reg);
    assert_eq!(back.as_ref(), Ok(&m), "{printed:?}");
    Some(m)
}

/// Parses `data` and verifies what parses. A panic here is a bug.
pub fn verifies_without_panic(data: &[u8], reg: &Registry) {
    if let Ok(m) = parse_bytes(data, reg) {
        let _ = verify(&m, reg);
    }
}
