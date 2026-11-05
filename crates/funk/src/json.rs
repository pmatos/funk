//! A small JSON writer for funk's reports.

use std::fmt::{self, Write};

use funk_ir::text::is_escaped;

/// A JSON value.
#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Num(u64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(&'static str, Json)>),
}

impl Json {
    /// A string value.
    pub fn str(s: impl Into<String>) -> Json {
        Json::Str(s.into())
    }

    /// The value as compact JSON text.
    pub fn render(&self) -> String {
        let mut out = String::new();
        self.write(&mut out);
        out
    }

    fn write(&self, out: &mut String) {
        match self {
            Json::Null => out.push_str("null"),
            Json::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Json::Num(n) => out.push_str(&n.to_string()),
            Json::Str(s) => write_str(out, s),
            Json::Arr(items) => {
                out.push('[');
                for (i, x) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    x.write(out);
                }
                out.push(']');
            }
            Json::Obj(fields) => {
                out.push('{');
                for (i, (k, v)) in fields.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write_str(out, k);
                    out.push(':');
                    v.write(out);
                }
                out.push('}');
            }
        }
    }
}

/// Writes a JSON string. Every character that a fir string escapes, such as
/// a control or a bidirectional override, is escaped here too, so a report
/// carries no hidden characters.
fn write_str(out: &mut String, s: &str) {
    out.push('"');
    let _ = escape(out, s);
    out.push('"');
}

/// Writes the characters of `s` as they appear inside a JSON string. Runs
/// of characters that need no escape are written whole.
pub fn escape(out: &mut impl Write, s: &str) -> fmt::Result {
    let mut unwritten = 0;
    for (i, c) in s.char_indices() {
        let short = match c {
            '"' => Some("\\\""),
            '\\' => Some("\\\\"),
            '\n' => Some("\\n"),
            '\t' => Some("\\t"),
            '\r' => Some("\\r"),
            c if is_escaped(c) => None,
            _ => continue,
        };
        out.write_str(&s[unwritten..i])?;
        unwritten = i + c.len_utf8();
        match short {
            Some(e) => out.write_str(e)?,
            None => {
                for unit in c.encode_utf16(&mut [0; 2]) {
                    write!(out, "\\u{unit:04x}")?;
                }
            }
        }
    }
    out.write_str(&s[unwritten..])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strings_are_escaped() {
        let v = Json::Obj(vec![
            (
                "s",
                Json::str("a\"b\\c\n\u{1}\u{2028}é\u{85}\u{202e}\u{e007f}"),
            ),
            ("n", Json::Num(3)),
            ("x", Json::Arr(vec![Json::Null, Json::Bool(true)])),
        ]);
        assert_eq!(
            v.render(),
            r#"{"s":"a\"b\\c\n\u0001\u2028é\u0085\u202e\udb40\udc7f","n":3,"x":[null,true]}"#
        );
    }
}
