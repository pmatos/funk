import Fir.Validation.Rules
import Fir.Text.Lexical

/-!
The rules of validation are propositions. The _validation check_ decides
them: it lists the rules that a module breaks, each as a _problem_ said in
words, and the list is empty exactly when the module is valid
(`Module.problems_eq_nil_iff`). It is written once for every dialect, so for
the core dialect it covers every op. `fir-ref validate` runs it (#10), and
`funk verify` (#9) must give the same verdict on every module.

A problem says what is wrong for people, and where: the function, the block,
the index of the op in its block and the op's location reference, each when
it applies. Tools compare whether a module is valid, never the words.
Symbols, names and labels appear in their canonical spelling, as the text
writes them, so a problem's message holds no line break and no hidden
character, whatever the module.

# Decidable dialect rules

The general rules can be decided for every dialect, given a way to compare
its types. A dialect's own rules, `validTy` and `validOp`, are propositions
that the dialect states, and the check must decide them too. So the check
asks of a dialect two things, and nothing more:

* `DecidableEq d.Ty`, to compare the types of operands, results and block
  arguments with those that the op instances and blocks expect;
* an instance of `DecidableDialectValidation d`, below, which decides its
  two rules.

The core dialect gives both: its types derive `DecidableEq`, and its rules
are decided in the section on the core dialect's decidable rules.
ADR-2026-10-30-1740 records why the check asks for these and no more.
-/

namespace Fir

variable {d : Dialect}

/--
A dialect whose own rules of validation can be decided: whether a type is
valid, and whether an op obeys the dialect's rule in its context.
-/
class DecidableDialectValidation (d : Dialect) [DialectValidation d] where
  decValidTy : ∀ t : d.Ty, Decidable (validTy t)
  decValidOp : ∀ (ctx : OpContext d) (o : d.Op), Decidable (validOp ctx o)

instance [DialectValidation d] [DecidableDialectValidation d] (t : d.Ty) :
    Decidable (validTy t) :=
  DecidableDialectValidation.decValidTy t

instance [DialectValidation d] [DecidableDialectValidation d] (ctx : OpContext d) (o : d.Op) :
    Decidable (validOp ctx o) :=
  DecidableDialectValidation.decValidOp ctx o

instance [DecidableEq d.Ty] : DecidableEq (FuncType d) := fun a b =>
  if h : a.params = b.params ∧ a.results = b.results then
    isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl⟩)

/--
A broken rule: what is wrong, in words for people, and where it is. `func` is
the symbol of the function, `block` the label of the block, `op` the index
of the op in its block and `loc` the op's location reference, each when the
rule is about one. A rule about a block has the location reference of its
first op.
-/
structure Problem where
  message : String
  func : Option Name := none
  block : Option Name := none
  op : Option Nat := none
  loc : Option LocRef := none
  deriving Repr, BEq

/-- A value, as the text writes it: `%x`, or `%"x y"` for a value whose name
is not a name. -/
def valueRef (x : Name) : String := "%" ++ if isName x then x else Text.quote x

/-- A block label, as the text writes it: `^l`, or `^"l m"` for a label that
is not a name. -/
def labelRef (l : Name) : String := "^" ++ if isName l then l else Text.quote l

/--
What the check of a function looks up in its module: the type of the
function that each symbol names, and whether the location table has a
reference. A module builds both as hash tables, once.
-/
structure Lookup (d : Dialect) where
  symbols : Name → Option (FuncType d)
  hasLoc : LocRef → Bool

/-- A lookup that agrees with a module context: the same symbols, and the
same references. -/
structure Lookup.Agrees (lk : Lookup d) (ctx : ModuleContext d) : Prop where
  symbols : lk.symbols = ctx.symbols
  hasLoc : ∀ r, lk.hasLoc r = true ↔ r ∈ ctx.locKeys

end Fir
