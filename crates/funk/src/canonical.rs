//! The canonical text of a module, compared with a file or streamed out,
//! never held whole: the canonical text of nested regions grows with the
//! square of their depth (ADR-2026-10-30-1333), so it can be far larger
//! than the file it comes from.

use std::fmt::{self, Display, Write};

use funk_ir::Module;
use funk_ir::text::write_module;

use crate::json;

/// Whether `bytes` are the canonical text of `m`. The printer stops at the
/// first byte that differs.
pub fn is_canonical(m: &Module, bytes: &[u8]) -> bool {
    let mut rest = Rest(bytes);
    write_module(&mut rest, m).is_ok() && rest.0.is_empty()
}

/// The bytes of a file that the printed text has not reached yet. A write
/// that does not match them fails.
struct Rest<'a>(&'a [u8]);

impl Write for Rest<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        match self.0.strip_prefix(s.as_bytes()) {
            Some(rest) => {
                self.0 = rest;
                Ok(())
            }
            None => Err(fmt::Error),
        }
    }
}

/// The canonical text of a module, written piece by piece.
pub struct Printed<'a>(pub &'a Module);

impl Display for Printed<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_module(f, self.0)
    }
}

/// The canonical text of a module as it appears inside a JSON string,
/// written piece by piece.
pub struct JsonText<'a>(pub &'a Module);

impl Display for JsonText<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_module(&mut Escaped(f), self.0)
    }
}

/// A sink that escapes what it is given for a JSON string. Each piece is
/// whole characters, so escaping piece by piece escapes the whole text.
struct Escaped<W>(W);

impl<W: Write> Write for Escaped<W> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        json::escape(&mut self.0, s)
    }
}

#[cfg(test)]
mod tests {
    use funk_ir::{Registry, parse, print};

    use super::*;

    const TEXT: &str =
        "func @\"a\\u{202e}\"() {\n^e:\n  ret @0\n}\n\nlocs {\n  @0 = name(\"q\\\"\\n\")\n}\n";

    fn module() -> Module {
        parse(TEXT, &Registry::core()).unwrap()
    }

    #[test]
    fn only_the_whole_canonical_text_is_canonical() {
        let m = module();
        assert!(is_canonical(&m, TEXT.as_bytes()));
        assert!(!is_canonical(&m, &TEXT.as_bytes()[..TEXT.len() - 1]));
        assert!(!is_canonical(&m, format!("{TEXT}\n").as_bytes()));
        assert!(!is_canonical(&m, TEXT.replace("  ret", "\tret").as_bytes()));
        assert!(!is_canonical(&m, b""));
    }

    #[test]
    fn streamed_texts_match_the_printed_text() {
        let m = module();
        assert_eq!(Printed(&m).to_string(), print(&m));
        let quoted = json::Json::str(print(&m)).render();
        let inside = quoted.strip_prefix('"').and_then(|s| s.strip_suffix('"'));
        assert_eq!(Some(JsonText(&m).to_string().as_str()), inside);
    }
}
