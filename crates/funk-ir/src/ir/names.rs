//! Which strings are names and words (`isName` and `isWord` in
//! `lean/Fir/Syntax/Module.lean`).
//!
//! A value name or a block label is one or more name characters: ASCII
//! letters, digits, `_` and `.`. A word is a name that starts with a letter or
//! `_`. A symbol may be any string; the text quotes it when it is not a word.

/// An ASCII letter or `_`: a character that may start a word.
pub fn is_word_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

/// A name character: an ASCII letter, a digit, `_` or `.`.
pub fn is_name_char(c: char) -> bool {
    is_word_start(c) || c.is_ascii_digit() || c == '.'
}

/// One or more name characters: a valid value name or block label.
pub fn is_name(s: &str) -> bool {
    !s.is_empty() && s.chars().all(is_name_char)
}

/// A name that starts with a letter or `_`.
pub fn is_word(s: &str) -> bool {
    let mut cs = s.chars();
    cs.next().is_some_and(is_word_start) && cs.all(is_name_char)
}

/// A word of a dialect other than the core: a word that holds a `.`, such
/// as `toy.cell` (`isDialectWord`). Every kind of item that a dialect
/// registers is one.
pub fn is_dialect_word(s: &str) -> bool {
    is_word(s) && s.contains('.')
}

/// The dialect that the word `w` names: the part before its first `.`, or
/// `None` for a bare word, which is the core's (ADR-2026-11-09-1543).
/// `toy.a.b` names `toy`.
pub fn word_dialect(w: &str) -> Option<&str> {
    w.split_once('.').map(|(d, _)| d)
}

/// Whether `s` is a float literal as the lexer reads it back
/// (`FloatLit.valid` in `lean/Fir/Syntax/Module.lean`): `-`, if any, a whole
/// number with no leading zeros, `.`, one or more digits, and `e` and an
/// integer with no leading zeros that is not `-0`, if any; or `0x` and one or
/// more lowercase hexadecimal digits.
pub fn is_float_lit(s: &str) -> bool {
    fn whole(s: &str) -> bool {
        s == "0" || (!s.starts_with('0') && !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()))
    }
    if let Some(hex) = s.strip_prefix("0x") {
        return !hex.is_empty()
            && hex
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b));
    }
    let body = s.strip_prefix('-').unwrap_or(s);
    let (mantissa, exp) = match body.split_once('e') {
        Some((m, e)) => (m, Some(e)),
        None => (body, None),
    };
    let Some((int, frac)) = mantissa.split_once('.') else {
        return false;
    };
    let exp_ok = exp.is_none_or(|e| match e.strip_prefix('-') {
        Some(mag) => mag != "0" && whole(mag),
        None => whole(e),
    });
    whole(int) && !frac.is_empty() && frac.bytes().all(|b| b.is_ascii_digit()) && exp_ok
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_and_words_follow_the_spec() {
        assert!(is_word("icmp") && is_word("gpu.launch") && is_word("_x"));
        assert!(!is_word("1f") && !is_word("") && !is_word("a-b"));
        assert!(is_name("0") && is_name("acc.1") && !is_name("") && !is_name("a b"));
        assert!(is_dialect_word("toy.cell") && !is_dialect_word("func"));
        assert!(!is_dialect_word(".x") && !is_dialect_word("dialects"));
    }

    #[test]
    fn a_word_names_the_dialect_before_its_first_dot() {
        assert_eq!(word_dialect("gpu.launch"), Some("gpu"));
        assert_eq!(word_dialect("toy.a.b"), Some("toy"));
        assert_eq!(word_dialect("add"), None);
    }
}
