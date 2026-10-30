//! Characters, strings and symbols (`lean/Fir/Text/Lexical.lean`).
//!
//! A string escapes the control characters (Unicode's Cc), the format
//! characters (Cf) of Unicode 16.0 and U+2028 and U+2029. Outside strings, a
//! text holds none of them except the tab and the line feed, not even in a
//! comment.

use crate::ir::names::is_word;

/// The format characters (category Cf) of Unicode 16.0, as ranges of code
/// points, first and last included (`formatChars`).
const FORMAT_CHARS: [(u32, u32); 21] = [
    (0xad, 0xad),
    (0x600, 0x605),
    (0x61c, 0x61c),
    (0x6dd, 0x6dd),
    (0x70f, 0x70f),
    (0x890, 0x891),
    (0x8e2, 0x8e2),
    (0x180e, 0x180e),
    (0x200b, 0x200f),
    (0x202a, 0x202e),
    (0x2060, 0x2064),
    (0x2066, 0x206f),
    (0xfeff, 0xfeff),
    (0xfff9, 0xfffb),
    (0x110bd, 0x110bd),
    (0x110cd, 0x110cd),
    (0x13430, 0x1343f),
    (0x1bca0, 0x1bca3),
    (0x1d173, 0x1d17a),
    (0xe0001, 0xe0001),
    (0xe0020, 0xe007f),
];

/// A character that a string escapes (`isEscaped`).
pub fn is_escaped(c: char) -> bool {
    let n = u32::from(c);
    n < 0x20
        || (0x7f..=0x9f).contains(&n)
        || n == 0x2028
        || n == 0x2029
        || FORMAT_CHARS.iter().any(|&(a, b)| a <= n && n <= b)
}

/// A character that a text may hold outside strings, comments included
/// (`allowedOutsideStrings`).
pub fn allowed_outside_strings(c: char) -> bool {
    c == '\t' || c == '\n' || !is_escaped(c)
}

/// Appends the canonical spelling of one character inside a string
/// (`escapeChar`).
fn push_escaped(out: &mut String, c: char) {
    match c {
        '"' => out.push_str("\\\""),
        '\\' => out.push_str("\\\\"),
        '\n' => out.push_str("\\n"),
        '\t' => out.push_str("\\t"),
        c if is_escaped(c) => out.push_str(&format!("\\u{{{:x}}}", u32::from(c))),
        c => out.push(c),
    }
}

/// The canonical spelling of a string, with its quotes (`quote`).
pub fn quote(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        push_escaped(&mut out, c);
    }
    out.push('"');
    out
}

/// The canonical spelling of a symbol: `@` and its name, quoted unless the
/// name is a word (`printSymbol`).
pub fn print_symbol(s: &str) -> String {
    if is_word(s) {
        format!("@{s}")
    } else {
        format!("@{}", quote(s))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strings_have_one_spelling() {
        assert_eq!(quote("a\"b\\c\n\u{1}é"), "\"a\\\"b\\\\c\\n\\u{1}é\"");
        assert_eq!(
            quote("\u{202e}\u{2066}\u{feff}\u{85}\u{2028}"),
            "\"\\u{202e}\\u{2066}\\u{feff}\\u{85}\\u{2028}\""
        );
        assert!(
            ['"', '\\', '\t', '\n', 'é']
                .iter()
                .all(|&c| allowed_outside_strings(c))
        );
        let hidden = [
            '\r', '\u{85}', '\u{200e}', '\u{202e}', '\u{2066}', '\u{feff}', '\u{2028}',
        ];
        assert!(hidden.iter().all(|&c| !allowed_outside_strings(c)));
        assert_eq!(print_symbol("sum"), "@sum");
        assert_eq!(print_symbol("1"), "@\"1\"");
        assert_eq!(print_symbol("a\nb"), "@\"a\\nb\"");
        assert_eq!(print_symbol(""), "@\"\"");
    }
}
