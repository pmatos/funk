//! What funk reports for each file, as text for people and as JSON for
//! agents (ADR-2026-10-30-1032).
//!
//! The JSON report of a file says whether the parser rejected it
//! (`parse-error`), validation rejected it (`validation-error`), or both
//! accepted it (`accepted`). A parse error carries a text position; a
//! validation error carries the IR location of the op or block it is about.

use std::collections::HashMap;
use std::fmt::Write;

use funk_ir::{Diagnostic, LocTable, ParseError};

use crate::json::Json;

/// The verdict on one file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Accepted,
    ParseError,
    ValidationError,
    IoError,
}

impl Verdict {
    pub fn name(self) -> &'static str {
        match self {
            Verdict::Accepted => "accepted",
            Verdict::ParseError => "parse-error",
            Verdict::ValidationError => "validation-error",
            Verdict::IoError => "io-error",
        }
    }
}

/// One thing wrong with a file.
#[derive(Clone, Debug)]
pub enum Problem {
    Parse(ParseError),
    /// A broken rule, with the printed location its reference stands for.
    Validation(Diagnostic, Option<String>),
    Io(String),
}

impl Problem {
    /// The validation problems of a module, with their locations resolved
    /// through its table.
    pub fn validation(ds: Vec<Diagnostic>, locs: &LocTable) -> Vec<Problem> {
        let mut table = HashMap::new();
        for (r, l) in &locs.entries {
            table.entry(*r).or_insert(l);
        }
        ds.into_iter()
            .map(|d| {
                let shown = d.loc.and_then(|r| table.get(&r)).map(ToString::to_string);
                Problem::Validation(d, shown)
            })
            .collect()
    }

    /// The problem as one line for people.
    pub fn text(&self, file: &str) -> String {
        match self {
            Problem::Parse(e) => format!(
                "{file}:{}:{}: parse error: {}",
                e.pos.line, e.pos.col, e.reason
            ),
            Problem::Io(why) => format!("{file}: error: {why}"),
            Problem::Validation(d, shown) => {
                let path = d.path();
                let mut line = format!("{file}: validation error");
                if !path.is_empty() {
                    let _ = write!(line, " in {}", path.join(" "));
                }
                let _ = write!(line, ": {}", d.message);
                match (d.loc, shown) {
                    (Some(r), Some(l)) => {
                        let _ = write!(line, " (at {r} = {l})");
                    }
                    (Some(r), None) => {
                        let _ = write!(line, " (at {r})");
                    }
                    _ => {}
                }
                line
            }
        }
    }

    /// The problem as JSON.
    pub fn json(&self) -> Json {
        let opt = |s: &Option<String>| s.as_ref().map_or(Json::Null, |s| Json::str(s.clone()));
        match self {
            Problem::Parse(e) => Json::Obj(vec![
                ("kind", Json::str("parse-error")),
                ("message", Json::str(e.reason.clone())),
                ("line", Json::Num(e.pos.line as u64)),
                ("column", Json::Num(e.pos.col as u64)),
            ]),
            Problem::Io(why) => Json::Obj(vec![
                ("kind", Json::str("io-error")),
                ("message", Json::str(why.clone())),
            ]),
            Problem::Validation(d, shown) => Json::Obj(vec![
                ("kind", Json::str("validation-error")),
                ("message", Json::str(d.message.clone())),
                ("func", opt(&d.func)),
                ("block", opt(&d.block)),
                ("op", d.op.map_or(Json::Null, |i| Json::Num(i as u64))),
                (
                    "loc",
                    d.loc.map_or(Json::Null, |r| {
                        Json::Obj(vec![
                            ("ref", Json::Num(u64::from(r.0))),
                            ("location", opt(shown)),
                        ])
                    }),
                ),
            ]),
        }
    }
}

/// The report on one file.
#[derive(Debug)]
pub struct Report {
    pub file: String,
    pub verdict: Verdict,
    pub problems: Vec<Problem>,
    /// Further fields of the JSON report, such as `fmt`'s `canonical`.
    pub extra: Vec<(&'static str, Json)>,
}

impl Report {
    pub fn json(&self) -> String {
        let mut fields = vec![
            ("file", Json::str(self.file.clone())),
            ("verdict", Json::str(self.verdict.name())),
            (
                "diagnostics",
                Json::Arr(self.problems.iter().map(Problem::json).collect()),
            ),
        ];
        fields.extend(self.extra.iter().cloned());
        Json::Obj(fields).render()
    }
}

#[cfg(test)]
mod tests {
    use funk_ir::{LocRef, Location};

    use super::*;

    #[test]
    fn locations_resolve_in_time_linear_in_the_table() {
        let n = 100_000;
        let mut locs = LocTable::new();
        for _ in 0..n {
            locs.push(Location::Unknown);
        }
        locs.insert(LocRef(7), Location::Name("second".into()));
        let at = |r: u32| Diagnostic {
            message: "m".into(),
            func: None,
            block: None,
            op: None,
            loc: Some(LocRef(r)),
        };
        let mut ds: Vec<Diagnostic> = (0..n).map(|_| at(4_000_000_000)).collect();
        ds.push(at(7));
        let start = std::time::Instant::now();
        let ps = Problem::validation(ds, &locs);
        let secs = start.elapsed().as_secs();
        assert!(matches!(&ps[0], Problem::Validation(_, None)));
        assert!(matches!(&ps[n], Problem::Validation(_, Some(l)) if l == "unknown"));
        assert!(secs < 5, "took {secs} s");
    }
}
