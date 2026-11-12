import Fir.Validation.Rules
import Fir.Text.Lexical

/-!
The rules of validation are propositions. The _validation check_ decides
them: it lists the rules that a module breaks, each as a _problem_ said in
words, and the list is empty exactly when the module is valid, as the
section on checking modules proves. It is written once for every dialect,
so for the core dialect it covers every op. `fir-ref validate` runs it, and
`funk verify` must give the same verdict on every module.

A problem says what is wrong for people, and where: the function, the block,
the index of the op in its block and the op's location reference, each when
it applies. Tools compare whether a module is valid, never the words.
Symbols appear in their canonical spelling, as the text writes them, and a
value name or label that is not a name appears between quotes, escaped as a
string is. So a problem's message holds no line break and no hidden
character, whatever the module.

# Decidable dialect rules

The general rules can be decided for every dialect, given a way to compare
its types. A dialect's own rules, which of its types are valid, whether an
op obeys its op rule, whether a function obeys its function rule and
whether a region obeys the rule of its kind, and whether an item of a kind
it registers obeys its rule for items, are propositions that the dialect
states, and the check must decide them too. So the check asks of a dialect
two things, and nothing more:

* that its types can be compared for equality, to compare the types of
  operands, results and block arguments with those that the op instances
  and blocks expect;
* that its five rules can be decided, as the first definition below says.

The core dialect gives both: its types can be compared, and the last
section of this chapter decides its rules. ADR-2026-11-09-2257 records
why the check asks for these and no more.
-/

namespace Fir

variable {d : Dialect}

/--
A dialect whose own rules of validation can be decided: whether a type is
valid, whether an op obeys the dialect's rule in its context, whether a
function obeys the dialect's rule over a whole function, whether a region
obeys the rule of its kind, and whether an item obeys the dialect's rule
for items. A dialect that registers no kind of region or of item decides
the last two by the default.
-/
class DecidableDialectValidation (d : Dialect) [DialectValidation d] where
  decValidTy : ∀ t : d.Ty, Decidable (validTy t)
  decValidOp : ∀ (ctx : OpContext d) (o : d.Op), Decidable (validOp ctx o)
  decValidFunc : ∀ {host : Dialect} (v : DialectView d host) (ctx : FuncContext host)
    (f : Func host), Decidable (validFunc v ctx f)
  decValidRegion : ∀ {host : Dialect} (v : DialectView d host) (k : Name) (ctx : FuncContext host)
    (f : Func host) (r : Region host), Decidable (validRegion v k ctx f r) := by
    intros; exact inferInstanceAs (Decidable False)
  decValidItem : ∀ {host : Dialect} (v : DialectView d host) (ctx : FuncContext host)
    (i : DialectItem host), Decidable (validItem v ctx i) := by
    intros; exact inferInstanceAs (Decidable False)

instance [DialectValidation d] [DecidableDialectValidation d] (t : d.Ty) :
    Decidable (validTy t) :=
  DecidableDialectValidation.decValidTy t

instance [DialectValidation d] [DecidableDialectValidation d] (ctx : OpContext d) (o : d.Op) :
    Decidable (validOp ctx o) :=
  DecidableDialectValidation.decValidOp ctx o

instance [DialectValidation d] [DecidableDialectValidation d] {host : Dialect}
    (v : DialectView d host) (ctx : FuncContext host) (f : Func host) :
    Decidable (validFunc v ctx f) :=
  DecidableDialectValidation.decValidFunc v ctx f

instance [DialectValidation d] [DecidableDialectValidation d] {host : Dialect}
    (v : DialectView d host) (k : Name) (ctx : FuncContext host) (f : Func host)
    (r : Region host) : Decidable (validRegion v k ctx f r) :=
  DecidableDialectValidation.decValidRegion v k ctx f r

instance [DialectValidation d] [DecidableDialectValidation d] {host : Dialect}
    (v : DialectView d host) (ctx : FuncContext host) (i : DialectItem host) :
    Decidable (validItem v ctx i) :=
  DecidableDialectValidation.decValidItem v ctx i
instance [DecidableEq d.Ty] : DecidableEq (FuncType d) := fun a b =>
  if h : a.params = b.params ∧ a.results = b.results then
    isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl⟩)

/--
A broken rule: what is wrong, in words for people, and where it is. `func` is
the symbol of the function, `block` the label of the block, `op` the index
of the op in its block and `loc` the op's location reference, each when the
rule is about one. A rule about a block has the location reference of its
first op; a rule about a label that names more than one block has that of
the first such block.
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
