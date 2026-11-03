//! A small Rust lexer for G0's source check (`tests/g0.rs`): the strings,
//! identifiers and punctuation of a source, without its comments, and
//! without the items it compiles only for its own unit tests.

pub mod sources;

/// A token of Rust code.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok {
    /// A string literal's text between its quotes, escapes as written.
    Str(String),
    /// An identifier or keyword.
    Ident(String),
    /// Any other character that is not part of a number or a char literal.
    Punct(char),
}

fn at(cs: &[char], i: usize, s: &str) -> bool {
    s.chars()
        .enumerate()
        .all(|(k, c)| cs.get(i + k) == Some(&c))
}

/// The text of a string whose opening quote ends before `i`, and the index
/// after its closing quote.
fn string(cs: &[char], mut i: usize) -> (String, usize) {
    let mut s = String::new();
    while i < cs.len() && cs[i] != '"' {
        if cs[i] == '\\' && i + 1 < cs.len() {
            s.push(cs[i]);
            i += 1;
        }
        s.push(cs[i]);
        i += 1;
    }
    (s, i + 1)
}

/// The text of a raw string whose `r` ends before `i`, at its `#`s or its
/// quote, and the index after it; `None` if no raw string starts there.
fn raw_string(cs: &[char], mut i: usize) -> Option<(String, usize)> {
    let mut hashes = 0;
    while cs.get(i) == Some(&'#') {
        hashes += 1;
        i += 1;
    }
    if cs.get(i) != Some(&'"') {
        return None;
    }
    let close: String = std::iter::once('"')
        .chain(std::iter::repeat_n('#', hashes))
        .collect();
    let start = i + 1;
    let mut j = start;
    while j < cs.len() && !at(cs, j, &close) {
        j += 1;
    }
    Some((cs[start..j.min(cs.len())].iter().collect(), j + close.len()))
}

/// The tokens of `src`, without its comments.
pub fn tokens(src: &str) -> Vec<Tok> {
    let cs: Vec<char> = src.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < cs.len() {
        let c = cs[i];
        if c.is_whitespace() {
            i += 1;
        } else if at(&cs, i, "//") {
            while i < cs.len() && cs[i] != '\n' {
                i += 1;
            }
        } else if at(&cs, i, "/*") {
            let mut depth = 0;
            while i < cs.len() {
                if at(&cs, i, "/*") {
                    depth += 1;
                    i += 2;
                } else if at(&cs, i, "*/") {
                    depth -= 1;
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    i += 1;
                }
            }
        } else if c == '"' {
            let (s, j) = string(&cs, i + 1);
            out.push(Tok::Str(s));
            i = j;
        } else if c == '\'' {
            // A char literal, `'x'` or `'\n'`, or a lifetime, `'a`.
            if cs.get(i + 1) == Some(&'\\') {
                // The quote, the backslash and the escaped character, then
                // the rest of a `\u{…}` or `\x…` escape.
                i += 3;
                while i < cs.len() && cs[i] != '\'' {
                    i += 1;
                }
                i += 1;
            } else if cs.get(i + 2) == Some(&'\'') {
                i += 3;
            } else {
                i += 1;
            }
        } else if c.is_alphabetic() || c == '_' {
            let start = i;
            while i < cs.len() && (cs[i].is_alphanumeric() || cs[i] == '_') {
                i += 1;
            }
            let word: String = cs[start..i].iter().collect();
            let raw = (word == "r" || word == "br")
                .then(|| raw_string(&cs, i))
                .flatten();
            if let Some((s, j)) = raw {
                out.push(Tok::Str(s));
                i = j;
            } else if word == "b" && cs.get(i) == Some(&'"') {
                let (s, j) = string(&cs, i + 1);
                out.push(Tok::Str(s));
                i = j;
            } else {
                out.push(Tok::Ident(word));
            }
        } else if c.is_ascii_digit() {
            while i < cs.len() && (cs[i].is_alphanumeric() || cs[i] == '_') {
                i += 1;
            }
        } else {
            out.push(Tok::Punct(c));
            i += 1;
        }
    }
    out
}

fn is_cfg_test(ts: &[Tok]) -> bool {
    let want = [
        Tok::Punct('#'),
        Tok::Punct('['),
        Tok::Ident("cfg".into()),
        Tok::Punct('('),
        Tok::Ident("test".into()),
        Tok::Punct(')'),
        Tok::Punct(']'),
    ];
    ts.starts_with(&want)
}

/// The code of a source's tokens: each item marked `#[cfg(test)]` is cut,
/// up to the `;` that ends it or the brace that closes its body, outside
/// any bracket, as in `const X: [&str; 1] = ["br"];`.
pub fn code(ts: &[Tok]) -> Vec<Tok> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < ts.len() {
        if !is_cfg_test(&ts[i..]) {
            out.push(ts[i].clone());
            i += 1;
            continue;
        }
        i += 7;
        let mut depth = 0usize;
        while i < ts.len() {
            let t = &ts[i];
            i += 1;
            match t {
                Tok::Punct(';') if depth == 0 => break,
                Tok::Punct('{' | '(' | '[') => depth += 1,
                Tok::Punct(c @ ('}' | ')' | ']')) => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 && *c == '}' {
                        break;
                    }
                }
                _ => {}
            }
        }
    }
    out
}

/// The index of the bracket that closes the one at `open`, or the end.
fn closing(ts: &[Tok], open: usize) -> usize {
    let mut depth = 0usize;
    for (k, t) in ts.iter().enumerate().skip(open) {
        match t {
            Tok::Punct('{' | '(' | '[') => depth += 1,
            Tok::Punct('}' | ')' | ']') => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return k;
                }
            }
            _ => {}
        }
    }
    ts.len()
}

/// A module that a source compiles only for its unit tests,
/// `#[cfg(test)] mod name;` or `#[cfg(test)] mod name { … }`, and the file
/// that its `#[path = "…"]` names, if it has one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TestMod {
    pub name: String,
    pub path: Option<String>,
}

/// The test modules of a source's tokens, comments left out but the
/// `#[cfg(test)]` items kept.
pub fn test_modules(ts: &[Tok]) -> Vec<TestMod> {
    let mut out = Vec::new();
    let (mut test, mut path) = (false, None);
    let mut i = 0;
    while i < ts.len() {
        if ts[i] == Tok::Punct('#') && ts.get(i + 1) == Some(&Tok::Punct('[')) {
            let end = closing(ts, i + 1);
            let attr = &ts[(i + 2).min(end)..end];
            test |= is_cfg_test(&ts[i..]);
            if let [Tok::Ident(key), Tok::Punct('='), Tok::Str(p)] = attr
                && key == "path"
            {
                path = Some(p.clone());
            }
            i = end + 1;
            continue;
        }
        if ts[i] == Tok::Ident("pub".into()) {
            i += 1;
            if ts.get(i) == Some(&Tok::Punct('(')) {
                i = closing(ts, i) + 1;
            }
            continue;
        }
        if let (Tok::Ident(kw), Some(Tok::Ident(name))) = (&ts[i], ts.get(i + 1))
            && kw == "mod"
            && test
        {
            out.push(TestMod {
                name: name.clone(),
                path: path.clone(),
            });
        }
        (test, path) = (false, None);
        i += 1;
    }
    out
}

/// Each `enum` of the code and the names of its variants.
pub fn enum_variants(ts: &[Tok]) -> Vec<(String, Vec<String>)> {
    let mut out = Vec::new();
    for (k, t) in ts.iter().enumerate() {
        let (Tok::Ident(kw), Some(Tok::Ident(name))) = (t, ts.get(k + 1)) else {
            continue;
        };
        if kw != "enum" {
            continue;
        }
        let Some(open) = ts[k..].iter().position(|t| *t == Tok::Punct('{')) else {
            continue;
        };
        let mut depth = 0usize;
        let mut expect = true;
        let mut variants = Vec::new();
        for t in &ts[k + open..] {
            match t {
                Tok::Punct('{' | '(' | '[') => depth += 1,
                Tok::Punct('}' | ')' | ']') => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                Tok::Punct(',') if depth == 1 => expect = true,
                Tok::Ident(v) if depth == 1 && expect => {
                    variants.push(v.clone());
                    expect = false;
                }
                _ => {}
            }
        }
        out.push((name.clone(), variants));
    }
    out
}

#[test]
fn the_lexer_sees_code_only() {
    let src = r##"
//! "add" in a doc comment, and `Op::new("ret", here)`.
/* "sub" /* nested "mul" */ still "xor" */
fn f<'a>(x: &'a str) -> char {
    let _ = ("const", r#"br "quoted""#, b"or", '"', '\'', "\"ret\"");
    'x' // "and"
}
#[cfg(test)]
mod tests {
    fn g() { let _ = "call"; }
}
#[cfg(test)]
const ICMP: &str = "icmp";
#[cfg(test)]
const OPS: [&str; 2] = ["add", "sub"];
#[cfg(test)]
fn h() -> [u8; 1] { let _ = "ret"; [0; 1] }
#[cfg(test)]
struct S(&'static str);
enum E<T> { #[default] Add, Sub(T), CondBr { x: [u8; 2] }, Ret = 3 }
enum F { X }
"##;
    let ts = code(&tokens(src));
    let strs: Vec<&str> = ts
        .iter()
        .filter_map(|t| match t {
            Tok::Str(s) => Some(s.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(strs, ["const", "br \"quoted\"", "or", "\\\"ret\\\""]);
    assert!(!ts.contains(&Tok::Ident("tests".into())));
    assert!(!ts.contains(&Tok::Ident("ICMP".into())));
    assert!(!ts.contains(&Tok::Ident("OPS".into())));
    assert!(!ts.contains(&Tok::Ident("S".into())));
    let es = enum_variants(&ts);
    let names: Vec<&str> = es.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(names, ["E", "F"]);
    assert_eq!(es[0].1, ["Add", "Sub", "CondBr", "Ret"]);
    assert_eq!(es[1].1, ["X"]);
}

#[test]
fn the_lexer_finds_the_test_modules() {
    let src = r#"
#[cfg(test)]
mod more_tests;
#[cfg(test)]
#[path = "t.rs"]
pub(crate) mod tests;
#[path = "p.rs"] #[cfg(test)] mod inline { mod deeper; }
mod real;
#[cfg(not(test))]
mod not_a_test;
#[cfg(test)]
use std::fmt;
mod after_a_test_use;
"#;
    let found = test_modules(&tokens(src));
    let want = |name: &str, path: Option<&str>| TestMod {
        name: name.into(),
        path: path.map(String::from),
    };
    assert_eq!(
        found,
        [
            want("more_tests", None),
            want("tests", Some("t.rs")),
            want("inline", Some("p.rs")),
        ]
    );
}
