//! Parses any bytes: the parser must not panic, and what parses must print
//! and parse back to the same module.

#![no_main]

use std::sync::OnceLock;

use funk_ir::Registry;
use funk_ir::fuzz::parse_round_trips;
use libfuzzer_sys::fuzz_target;

fn registry() -> &'static Registry {
    static REGISTRY: OnceLock<Registry> = OnceLock::new();
    REGISTRY.get_or_init(Registry::core)
}

fuzz_target!(|data: &[u8]| {
    let _ = parse_round_trips(data, registry());
});
