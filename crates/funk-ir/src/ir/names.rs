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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_and_words_follow_the_spec() {
        assert!(is_word("icmp") && is_word("gpu.launch") && is_word("_x"));
        assert!(!is_word("1f") && !is_word("") && !is_word("a-b"));
        assert!(is_name("0") && is_name("acc.1") && !is_name("") && !is_name("a b"));
    }
}
