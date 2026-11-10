//! The effects of an op: what it may do beyond computing its results from
//! its operands (`Effects` in `lean/Fir/Execution/OpEffects.lean`,
//! ADR-2026-11-09-1541).
//!
//! Each op declares its set through [`OpSpec::effects`](crate::OpSpec::effects),
//! as each op of a Lean dialect does through `DialectEffects`, and
//! `tests/dialects/effects.cases` checks that the core's sets here are the
//! ones of `Core.Op.effects`. The memory-named effects name the dialect's own
//! memories, or every memory. No op uses them yet: the core dialect has no
//! memory (ADR-2026-11-09-1542).
//!
//! The spec proves each Lean declaration sound: an effect that an op leaves
//! out, it does not have. A pass may rely on a set here because it equals
//! the proved one.

use std::fmt;

/// The memories an effect touches: the listed ones, or every memory.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MemSet {
    /// These memories, and no other. The empty list touches no memory.
    These(Vec<String>),
    /// Every memory, as an external call may touch.
    Every,
}

impl MemSet {
    /// No memory.
    pub const NONE: MemSet = MemSet::These(Vec::new());

    /// Whether the set holds `memory`: it lists it, or is every memory.
    pub fn has(&self, memory: &str) -> bool {
        match self {
            MemSet::These(ms) => ms.iter().any(|m| m == memory),
            MemSet::Every => true,
        }
    }

    /// The join of two sets (`MemSet.join`): every memory, if either is, and
    /// otherwise the memories of both, each once, in order.
    pub fn join(&self, other: &MemSet) -> MemSet {
        match (self, other) {
            (MemSet::Every, _) | (_, MemSet::Every) => MemSet::Every,
            (MemSet::These(ms), MemSet::These(ns)) => {
                let mut out = ms.clone();
                for n in ns {
                    if !out.contains(n) {
                        out.push(n.clone());
                    }
                }
                MemSet::These(out)
            }
        }
    }

    /// The set with its memories in sorted order, each once: a set holds
    /// what it lists, whatever the order.
    pub fn sorted(&self) -> MemSet {
        match self {
            MemSet::Every => MemSet::Every,
            MemSet::These(ms) => {
                let mut ms = ms.clone();
                ms.sort();
                ms.dedup();
                MemSet::These(ms)
            }
        }
    }
}

/// An op's set of effects. Each memory-named effect names the memories it
/// touches; each other effect is there or not. The default is the empty set:
/// the op is pure.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Effects {
    /// The memories the op may read.
    pub reads: MemSet,
    /// The memories the op may write.
    pub writes: MemSet,
    /// The memories in which the op may allocate or free.
    pub allocates: MemSet,
    /// The op may end in immediate UB.
    pub may_ub: bool,
    /// On operands with no poison, a result of the op may be poison
    /// (ADR-2026-11-09-2249).
    pub may_poison: bool,
    /// The op may add an event to the trace of the run.
    pub observable: bool,
    /// The op is a terminator.
    pub control: bool,
}

impl Default for Effects {
    fn default() -> Effects {
        Effects::PURE
    }
}

impl Effects {
    /// The empty set: the op is pure.
    pub const PURE: Effects = Effects {
        reads: MemSet::NONE,
        writes: MemSet::NONE,
        allocates: MemSet::NONE,
        may_ub: false,
        may_poison: false,
        observable: false,
        control: false,
    };

    /// Every effect, on every memory: what an op declares when nothing
    /// narrower is known of it, as of an external call (`Effects.all`).
    pub const ALL: Effects = Effects {
        reads: MemSet::Every,
        writes: MemSet::Every,
        allocates: MemSet::Every,
        may_ub: true,
        may_poison: true,
        observable: true,
        control: true,
    };

    /// The join of two sets (`Effects.join`): each memory-named effect
    /// touches the memories of both, and every other effect is there when
    /// either has it.
    pub fn join(&self, other: &Effects) -> Effects {
        Effects {
            reads: self.reads.join(&other.reads),
            writes: self.writes.join(&other.writes),
            allocates: self.allocates.join(&other.allocates),
            may_ub: self.may_ub || other.may_ub,
            may_poison: self.may_poison || other.may_poison,
            observable: self.observable || other.observable,
            control: self.control || other.control,
        }
    }

    /// The effects of the set as a caller of its op sees them
    /// (`Effects.callerView`): every effect but control, since a terminator
    /// of a callee ends a block of the callee, not of its caller.
    pub fn caller_view(&self) -> Effects {
        Effects {
            control: false,
            ..self.clone()
        }
    }

    /// The set with each set of memories in sorted order, each once.
    pub fn sorted(&self) -> Effects {
        Effects {
            reads: self.reads.sorted(),
            writes: self.writes.sorted(),
            allocates: self.allocates.sorted(),
            ..self.clone()
        }
    }
}

/// Writes a set of effects as the shared case files do: `pure`, or the
/// effects joined by `,` in their order here, each memory-named one with its
/// memories, such as `reads(*)` or `writes(a+b)`.
impl fmt::Display for Effects {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut words = Vec::new();
        for (name, ms) in [
            ("reads", &self.reads),
            ("writes", &self.writes),
            ("allocates", &self.allocates),
        ] {
            match ms {
                MemSet::Every => words.push(format!("{name}(*)")),
                MemSet::These(ms) if !ms.is_empty() => {
                    words.push(format!("{name}({})", ms.join("+")));
                }
                MemSet::These(_) => {}
            }
        }
        for (name, has) in [
            ("may-ub", self.may_ub),
            ("may-poison", self.may_poison),
            ("observable", self.observable),
            ("control", self.control),
        ] {
            if has {
                words.push(name.to_string());
            }
        }
        if words.is_empty() {
            f.write_str("pure")
        } else {
            f.write_str(&words.join(","))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sets_print_as_the_case_files_write_them() {
        assert_eq!(Effects::PURE.to_string(), "pure");
        assert_eq!(Effects::default(), Effects::PURE);
        assert_eq!(
            Effects::ALL.to_string(),
            "reads(*),writes(*),allocates(*),may-ub,may-poison,observable,control"
        );
        let e = Effects {
            writes: MemSet::These(vec!["a".into(), "b".into()]),
            may_ub: true,
            ..Effects::PURE
        };
        assert_eq!(e.to_string(), "writes(a+b),may-ub");
        assert!(e.writes.has("b") && !e.writes.has("c") && !e.reads.has("a"));
        assert!(MemSet::Every.has("c"));
    }

    #[test]
    fn joins_keep_every_effect_of_either_side() {
        let these = |ms: &[&str]| MemSet::These(ms.iter().map(|m| m.to_string()).collect());
        assert_eq!(
            these(&["b", "a"]).join(&these(&["a", "c"])),
            these(&["b", "a", "c"])
        );
        assert_eq!(these(&["a"]).join(&MemSet::Every), MemSet::Every);
        assert_eq!(MemSet::Every.join(&MemSet::NONE), MemSet::Every);
        assert_eq!(these(&["b", "a", "b"]).sorted(), these(&["a", "b"]));
        let a = Effects {
            reads: these(&["m"]),
            may_ub: true,
            ..Effects::PURE
        };
        let b = Effects {
            may_poison: true,
            control: true,
            ..Effects::PURE
        };
        let j = a.join(&b);
        assert_eq!(j.to_string(), "reads(m),may-ub,may-poison,control");
        assert_eq!(j.caller_view().to_string(), "reads(m),may-ub,may-poison");
        assert_eq!(Effects::PURE.join(&Effects::PURE), Effects::PURE);
    }
}
