//! The tokens of fir text (`lean/Fir/Text/Lexical.lean`, "Tokens").
//!
//! Whitespace and comments may come before, between and after tokens.
//! Tokens are read by maximal munch, and a value, a label, a symbol written
//! as a word, a location reference, a word or an integer must not run into a
//! name character: `@1x` and `1.5` are errors, while `const-1` reads as
//! `const -1`.

use super::chars::{allowed_outside_strings, is_escaped};
use super::{ParseError, TextPos};
use crate::ir::names::{is_name_char, is_word, is_word_start};
use crate::ir::{Int, LocRef};

/// A token.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Tok {
    Value(String),
    Label(String),
    Sym(String),
    LocRef(LocRef),
    Word(String),
    Int(Int),
    Str(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Colon,
    Eq,
    Arrow,
    Eof,
}

impl Tok {
    /// How a message names the token.
    pub(super) fn describe(&self) -> String {
        match self {
            Tok::Value(v) => format!("value %{v}"),
            Tok::Label(l) => format!("label ^{l}"),
            Tok::Sym(s) => format!("symbol {}", super::chars::print_symbol(s)),
            Tok::LocRef(r) => format!("location reference {r}"),
            Tok::Word(w) => format!("word {w}"),
            Tok::Int(i) => format!("integer {i}"),
            Tok::Str(s) => format!("string {}", super::chars::quote(s)),
            Tok::LParen => "(".into(),
            Tok::RParen => ")".into(),
            Tok::LBrace => "{".into(),
            Tok::RBrace => "}".into(),
            Tok::Comma => ",".into(),
            Tok::Colon => ":".into(),
            Tok::Eq => "=".into(),
            Tok::Arrow => "->".into(),
            Tok::Eof => "the end of the text".into(),
        }
    }
}

/// A token and where it starts.
#[derive(Clone, Debug)]
pub(super) struct Token {
    pub tok: Tok,
    pub pos: TextPos,
}

/// Reads the tokens of a text one at a time, so that no list of them takes
/// memory (ADR-2026-10-30-1333).
pub(super) struct Lexer<'t> {
    text: &'t str,
    at: usize,
    line: usize,
    line_start: usize,
}

impl<'t> Lexer<'t> {
    /// A lexer at the start of `text`.
    pub(super) fn new(text: &'t str) -> Lexer<'t> {
        Lexer {
            text,
            at: 0,
            line: 1,
            line_start: 0,
        }
    }

    /// The next token, after any whitespace and comments: [`Tok::Eof`] at
    /// the end of the text.
    pub(super) fn next_token(&mut self) -> Result<Token, ParseError> {
        self.skip_blanks()?;
        let pos = self.pos();
        let tok = self.token()?;
        Ok(Token { tok, pos })
    }
}

fn err<T>(pos: TextPos, reason: impl Into<String>) -> Result<T, ParseError> {
    Err(ParseError {
        pos,
        reason: reason.into(),
    })
}

impl Lexer<'_> {
    fn pos(&self) -> TextPos {
        TextPos {
            line: self.line,
            col: self.at - self.line_start + 1,
        }
    }

    fn peek(&self) -> Option<char> {
        self.text[self.at..].chars().next()
    }

    fn peek2(&self) -> Option<char> {
        self.text[self.at..].chars().nth(1)
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.at += c.len_utf8();
        if c == '\n' {
            self.line += 1;
            self.line_start = self.at;
        }
        Some(c)
    }

    fn check_outside(&self, c: char) -> Result<(), ParseError> {
        if allowed_outside_strings(c) {
            return Ok(());
        }
        err(
            self.pos(),
            format!("{} is not allowed outside strings", code_point(c)),
        )
    }

    fn skip_blanks(&mut self) -> Result<(), ParseError> {
        while let Some(c) = self.peek() {
            match c {
                ' ' | '\t' | '\n' => {
                    self.bump();
                }
                '/' if self.peek2() == Some('/') => {
                    while let Some(c) = self.peek() {
                        if c == '\n' {
                            break;
                        }
                        self.check_outside(c)?;
                        self.bump();
                    }
                }
                _ => return Ok(()),
            }
        }
        Ok(())
    }

    fn take_name_chars(&mut self) -> String {
        let start = self.at;
        while self.peek().is_some_and(is_name_char) {
            self.bump();
        }
        self.text[start..self.at].to_string()
    }

    fn token(&mut self) -> Result<Tok, ParseError> {
        let pos = self.pos();
        let Some(c) = self.peek() else {
            return Ok(Tok::Eof);
        };
        self.check_outside(c)?;
        let simple = match c {
            '(' => Some(Tok::LParen),
            ')' => Some(Tok::RParen),
            '{' => Some(Tok::LBrace),
            '}' => Some(Tok::RBrace),
            ',' => Some(Tok::Comma),
            ':' => Some(Tok::Colon),
            '=' => Some(Tok::Eq),
            _ => None,
        };
        if let Some(tok) = simple {
            self.bump();
            return Ok(tok);
        }
        match c {
            '%' | '^' => {
                self.bump();
                let name = self.take_name_chars();
                if name.is_empty() {
                    let what = if c == '%' { "a value name" } else { "a label" };
                    return err(pos, format!("{c} must be followed by {what}"));
                }
                Ok(if c == '%' {
                    Tok::Value(name)
                } else {
                    Tok::Label(name)
                })
            }
            '@' => self.at_sign(pos),
            '"' => Ok(Tok::Str(self.string()?)),
            '-' if self.peek2() == Some('>') => {
                self.bump();
                self.bump();
                Ok(Tok::Arrow)
            }
            '-' | '0'..='9' => self.integer(pos),
            c if is_word_start(c) => Ok(Tok::Word(self.take_name_chars())),
            c => err(pos, format!("unexpected character {}", code_point(c))),
        }
    }

    fn at_sign(&mut self, pos: TextPos) -> Result<Tok, ParseError> {
        self.bump();
        match self.peek() {
            Some(c) if c.is_ascii_digit() => {
                let num_pos = self.pos();
                let digits = self.nat_digits(num_pos)?;
                match digits.parse::<u32>() {
                    Ok(n) => Ok(Tok::LocRef(LocRef(n))),
                    Err(_) => err(
                        num_pos,
                        format!(
                            "location reference @{digits} is out of range: it must be below 2^32"
                        ),
                    ),
                }
            }
            Some(c) if is_word_start(c) => Ok(Tok::Sym(self.take_name_chars())),
            Some('"') => {
                let name = self.string()?;
                if is_word(&name) {
                    return err(pos, format!("the symbol @\"{name}\" is written @{name}"));
                }
                Ok(Tok::Sym(name))
            }
            _ => err(
                pos,
                "@ must be followed by a symbol or a location reference",
            ),
        }
    }

    /// The digits of a `nat`, which must not run into a name character.
    fn nat_digits(&mut self, pos: TextPos) -> Result<String, ParseError> {
        let start = self.at;
        if self.peek() == Some('0') {
            self.bump();
        } else {
            while self.peek().is_some_and(|c| c.is_ascii_digit()) {
                self.bump();
            }
        }
        self.no_name_char_after(pos)?;
        Ok(self.text[start..self.at].to_string())
    }

    fn no_name_char_after(&self, pos: TextPos) -> Result<(), ParseError> {
        match self.peek() {
            Some(c) if is_name_char(c) => err(
                pos,
                format!(
                    "a number must not run into the name character {c:?}: numbers have no leading zeros, and fir has no float literals"
                ),
            ),
            _ => Ok(()),
        }
    }

    fn integer(&mut self, pos: TextPos) -> Result<Tok, ParseError> {
        let negative = self.peek() == Some('-');
        if negative {
            self.bump();
            match self.peek() {
                Some('1'..='9') => {}
                Some('0') => return err(pos, "-0 is not an integer"),
                _ => return err(pos, "- must start a negative integer or ->"),
            }
        }
        let digits = self.nat_digits(pos)?;
        let spelled = if negative {
            format!("-{digits}")
        } else {
            digits
        };
        let int = Int::parse(&spelled).expect("the lexer reads canonical integers");
        Ok(Tok::Int(int))
    }

    fn string(&mut self) -> Result<String, ParseError> {
        let open = self.pos();
        self.bump();
        let mut out = String::new();
        loop {
            let pos = self.pos();
            match self.bump() {
                None => return err(open, "the string is not closed"),
                Some('"') => return Ok(out),
                Some('\\') => out.push(self.escape(pos)?),
                Some(c) if is_escaped(c) => {
                    return err(
                        pos,
                        format!("{} must be escaped in a string", code_point(c)),
                    );
                }
                Some(c) => out.push(c),
            }
        }
    }

    fn escape(&mut self, pos: TextPos) -> Result<char, ParseError> {
        match self.bump() {
            Some('\\') => Ok('\\'),
            Some('"') => Ok('"'),
            Some('n') => Ok('\n'),
            Some('t') => Ok('\t'),
            Some('u') if self.peek() == Some('{') => {
                self.bump();
                let start = self.at;
                while self
                    .peek()
                    .is_some_and(|c| c.is_ascii_digit() || ('a'..='f').contains(&c))
                {
                    self.bump();
                }
                let hex = self.text[start..self.at].to_string();
                if self.bump() != Some('}') || hex.is_empty() {
                    return err(
                        pos,
                        "\\u{ must be followed by lowercase hexadecimal digits and }",
                    );
                }
                let c = u32::from_str_radix(&hex, 16).ok().and_then(char::from_u32);
                match c {
                    Some(c) if hex.len() > 1 && hex.starts_with('0') => err(
                        pos,
                        format!(
                            "\\u{{{hex}}} has a leading zero: write \\u{{{:x}}}",
                            u32::from(c)
                        ),
                    ),
                    Some(c) if c == '\n' || c == '\t' => err(
                        pos,
                        format!("{} is written {:?} in a string", code_point(c), c),
                    ),
                    Some(c) if is_escaped(c) => Ok(c),
                    Some(c) => err(
                        pos,
                        format!("{} is written as itself, not as an escape", code_point(c)),
                    ),
                    None => err(pos, format!("\\u{{{hex}}} is not a Unicode scalar value")),
                }
            }
            _ => err(pos, "a string escape is \\\\, \\\", \\n, \\t or \\u{h}"),
        }
    }
}

/// How a message names a character: `U+000D`.
fn code_point(c: char) -> String {
    format!("U+{:04X}", u32::from(c))
}
