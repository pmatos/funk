//! fir's one canonical text format (P3, ADR-2026-10-29-2014;
//! `lean/Fir/Text/`).
//!
//! [`parse`] reads a text in two steps: it reads the tokens by the one
//! grammar that covers every dialect, then decodes what the grammar leaves
//! generic through the [`Registry`]. [`print`] writes the one canonical
//! spelling. `parse(print(m)) == m` for every well-formed module, and
//! `print(parse(t)) == t` for every text printed from one
//! (ADR-2026-10-30-0815).

mod chars;
mod decode;
mod grammar;
mod lexer;
mod print;
mod syntax;

use std::fmt;

pub use chars::{allowed_outside_strings, is_escaped, print_symbol, quote};
pub(crate) use print::Commas;
pub use print::{print, print_func, print_op};

use crate::ir::Module;
use crate::registry::Registry;

/// A position in a text: a line from 1, and a column in UTF-8 bytes from 1
/// (`TextPos` in `lean/Fir/Text/RoundTrip.lean`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TextPos {
    /// The line, from 1.
    pub line: usize,
    /// The column, in UTF-8 bytes from 1.
    pub col: usize,
}

impl fmt::Display for TextPos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

/// Why the parser rejects a text, and where. The reason is for people;
/// tools compare only whether a text is rejected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    /// Where the reason applies.
    pub pos: TextPos,
    /// Why the text is rejected.
    pub reason: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.pos, self.reason)
    }
}

impl std::error::Error for ParseError {}

/// Parses a text into a module, decoding its ops and types through `reg`.
///
/// A text with several errors is rejected at the first error of the
/// earliest phase: characters and tokens, then the grammar, then decoding,
/// which checks each function's definitions before its ops
/// (ADR-2026-10-30-1032).
pub fn parse(text: &str, reg: &Registry) -> Result<Module, ParseError> {
    let tokens = lexer::tokenize(text)?;
    let syntax = grammar::module(tokens)?;
    decode::module(syntax, reg)
}

/// Parses the bytes of a file. Bytes that are not UTF-8 are a parse error at
/// the first byte that is not.
pub fn parse_bytes(bytes: &[u8], reg: &Registry) -> Result<Module, ParseError> {
    match std::str::from_utf8(bytes) {
        Ok(text) => parse(text, reg),
        Err(e) => {
            let valid = &bytes[..e.valid_up_to()];
            let line = valid.iter().filter(|&&b| b == b'\n').count() + 1;
            let line_start = valid.iter().rposition(|&b| b == b'\n').map_or(0, |i| i + 1);
            let pos = TextPos {
                line,
                col: valid.len() - line_start + 1,
            };
            Err(ParseError {
                pos,
                reason: "the text is not UTF-8".into(),
            })
        }
    }
}
