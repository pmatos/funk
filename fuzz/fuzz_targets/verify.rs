//! Parses any bytes and verifies what parses: the verifier must not panic.

#![no_main]

use std::sync::OnceLock;

use funk_ir::Registry;
use funk_ir::fuzz::verifies_without_panic;
use libfuzzer_sys::fuzz_target;

fn registry() -> &'static Registry {
    static REGISTRY: OnceLock<Registry> = OnceLock::new();
    REGISTRY.get_or_init(Registry::core)
}

fuzz_target!(|data: &[u8]| {
    verifies_without_panic(data, registry());
});
