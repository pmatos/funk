//! What funk reports for each file, as text for people and as JSON for
//! agents (ADR-2026-10-30-1032, ADR-2026-10-30-1233).
//!
//! The JSON report of a file says whether the parser rejected it
//! (`parse-error`), validation rejected it (`validation-error`), the backend
//! cannot lower it (`unsupported`), or all accepted it (`accepted`). A parse
//! error carries a text position; a validation error and an unsupported part
//! carry the IR location of the op or block they are about.

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
    Unsupported,
    IoError,
    ToolError,
}

impl Verdict {
    pub fn name(self) -> &'static str {
        match self {
            Verdict::Accepted => "accepted",
            Verdict::ParseError => "parse-error",
            Verdict::ValidationError => "validation-error",
            Verdict::Unsupported => "unsupported",
            Verdict::IoError => "io-error",
            Verdict::ToolError => "tool-error",
        }
    }
}

/// What a problem with an IR location is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// A broken rule of validation.
    Validation,
    /// A part of a valid module that the backend cannot lower.
    Unsupported,
}

impl Kind {
    fn name(self) -> &'static str {
        match self {
            Kind::Validation => "validation-error",
            Kind::Unsupported => "unsupported",
        }
    }

    fn text(self) -> &'static str {
        match self {
            Kind::Validation => "validation error",
            Kind::Unsupported => "unsupported",
        }
    }
}

/// One thing wrong with a file.
#[derive(Clone, Debug)]
pub enum Problem {
    Parse(ParseError),
    /// A problem at an IR location, with the printed location its reference
    /// stands for.
    Located(Kind, Diagnostic, Option<String>),
    Io(String),
    /// The assembler or the linker could not run, or failed.
    Tool(String),
}

impl Problem {
    /// Problems of a module, with their locations resolved through its
    /// table.
    pub fn located(kind: Kind, ds: Vec<Diagnostic>, locs: &LocTable) -> Vec<Problem> {
        let mut table = HashMap::new();
        for (r, l) in &locs.entries {
            table.entry(*r).or_insert(l);
        }
        ds.into_iter()
            .map(|d| {
                let shown = d.loc.and_then(|r| table.get(&r)).map(ToString::to_string);
                Problem::Located(kind, d, shown)
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
            Problem::Io(why) | Problem::Tool(why) => format!("{file}: error: {why}"),
            Problem::Located(kind, d, shown) => {
                let path = d.path();
                let mut line = format!("{file}: {}", kind.text());
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
            Problem::Tool(why) => Json::Obj(vec![
                ("kind", Json::str("tool-error")),
                ("message", Json::str(why.clone())),
            ]),
            Problem::Located(kind, d, shown) => Json::Obj(vec![
                ("kind", Json::str(kind.name())),
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
        let ps = Problem::located(Kind::Validation, ds, &locs);
        let secs = start.elapsed().as_secs();
        assert!(matches!(&ps[0], Problem::Located(_, _, None)));
        assert!(matches!(&ps[n], Problem::Located(_, _, Some(l)) if l == "unknown"));
        assert!(secs < 5, "took {secs} s");
    }
}
