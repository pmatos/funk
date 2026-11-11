import Fir.Sum.Names
import Fir.Validation.Check
import Fir.Execution.Propagation

/-!
A module that holds the ops of several dialects is a module of their _sum_,
one dialect that holds them all (ADR-2026-11-09-1543). The sum is built one
dialect at a time: `base ⊞ e` adds the dialect `e` to the dialect `base`,
which may itself be a sum. So `core ⊞ a ⊞ b` holds three dialects, and a
sum holds any number.

The added dialect `e` extends its base. It has ops `e.Op` and types of its
own `e.Ty`, and its ops are used at the types of `base.over e`: the base's
types and its own. So an op of `e` can take and give values of the base's
types, as an extension op takes a core integer. The base is what `e`
depends on, and `e` may name the base's types. `e` states each class of a
dialect for `base.over e`: its signature, its text, its rules, its poison
classes and effects, its semantics and its calls. A dialect that has no types of its
own takes `Empty` for them.

The sum's ops are those of the base and those of `e`, and its types are
those of the base and those of `e`. Each class of a dialect is lifted to
the sum, by routing each op and each type to the side it belongs to:

* an op or a type of the base has what the base gives it. Its types are
  the base's, written into the sum's;
* an op or a type of `e` has what `base.over e` gives it;
* reading an op or a type sends its name to a side by its prefix: a name
  whose dialect is `e`'s name goes to `e`, and every other name to the
  base. So the base never sees a word of `e`, and `e` sees its own words.
  A name holds no `.`, so that `e`'s words name it;
* an op's attributes go with the op, to the side that its name picks. They
  are generic terms, read by the op's own dialect, so the sum does not
  route them on their own. The dialect-set laws say which dialects their
  words may name;
* a function of the sum obeys the function rule of each side, and each
  rule sees the whole function through its own view;
* the sum registers the region kinds of both sides. A region of a kind that
  the base registers obeys the base's rule for it, and a region of any other
  kind `e`'s rule, each through its own view. The laws of names say that
  `e`'s kinds are words of `e`'s name, so the base registers none of them;
* the sum registers the kinds of item of both sides in the same way. An
  item of a kind that the base registers obeys the base's rule, and an item
  of any other kind `e`'s rule, each through its own view.

An op of the base sees the context of a function only when the base can
write it: the symbols whose types are all the base's, and the function's
result types when they are all the base's. In a function whose result
types the base cannot write, no op of the base is valid, since the base has
no rule that could judge it. That is a limit of this sum: a base's ops
carry the base's types only, so the core's `br`, `ret` and `call` cannot
pass a value of `e`'s own types.

This section gives, in order: an extension and the sum, the meaning of the
summed types, how values move between the base's types and the sum's, and
each class of the sum. The section on the sum's laws proves that the sum
of lawful dialects is lawful.
-/

namespace Fir

/-!
# Extensions and sums
-/

/-- The dialect `e` over the base `base`: the ops of `e`, used at the
base's types and at `e`'s own. -/
abbrev Dialect.over (base e : Dialect) : Dialect := ⟨e.Op, base.Ty ⊕ e.Ty⟩

/-- The sum of the base `base` and the dialect `e` over it: the ops of
both, and the types of both. -/
def Dialect.sum (base e : Dialect) : Dialect := ⟨base.Op ⊕ e.Op, base.Ty ⊕ e.Ty⟩

@[inherit_doc] infixl:65 " ⊞ " => Dialect.sum

/-!
# Summed types
-/

/-- A type with no values: the own types of a dialect that has none. -/
instance instTyDenoteEmpty : TyDenote Empty := ⟨fun t => nomatch t⟩

/-- A type of a sum denotes what it denotes on its own side. -/
instance instTyDenoteSum {A B : Type} [TyDenote A] [TyDenote B] : TyDenote (A ⊕ B) where
  toType
    | .inl t => ⟦t⟧
    | .inr t => ⟦t⟧

/-- A value of a summed type is poison when it is on its own side. -/
instance instTyPoisonSum {A B : Type} [TyDenote A] [TyDenote B] [TyPoison A] [TyPoison B] :
    TyPoison (A ⊕ B) where
  IsPoison {t} := match t with
    | .inl t => TyPoison.IsPoison (Ty := A) (t := t)
    | .inr t => TyPoison.IsPoison (Ty := B) (t := t)

/-- A value of a summed type is refined as on its own side. -/
instance instTyRefinementSum {A B : Type} [TyDenote A] [TyDenote B] [TyRefinement A]
    [TyRefinement B] : TyRefinement (A ⊕ B) where
  IsRefinedBy {t} := match t with
    | .inl t => TyRefinement.IsRefinedBy (Ty := A) (t := t)
    | .inr t => TyRefinement.IsRefinedBy (Ty := B) (t := t)

/-- A value of `Empty` is never poison: there is none. -/
instance instTyPoisonEmpty : TyPoison Empty := ⟨fun {t} => nomatch t⟩

/-- A value of `Empty` refines nothing: there is none. -/
instance instTyRefinementEmpty : TyRefinement Empty := ⟨fun {t} => nomatch t⟩

section
variable {base e : Dialect} [TyDenote base.Ty] [TyDenote e.Ty]

/-- The types of a sum are summed types. -/
instance instTyDenoteSumTy : TyDenote (base ⊞ e).Ty := instTyDenoteSum

instance instTyPoisonSumTy [TyPoison base.Ty] [TyPoison e.Ty] : TyPoison (base ⊞ e).Ty :=
  instTyPoisonSum

instance instTyRefinementSumTy [TyRefinement base.Ty] [TyRefinement e.Ty] :
    TyRefinement (base ⊞ e).Ty :=
  instTyRefinementSum

end

/-- The ops of a sum can be compared when both sides' can. -/
instance instDecidableEqSumOp {base e : Dialect} [DecidableEq base.Op] [DecidableEq e.Op] :
    DecidableEq (base ⊞ e).Op :=
  inferInstanceAs (DecidableEq (base.Op ⊕ e.Op))

/-- The types of a sum can be compared when both sides' can. -/
instance instDecidableEqSumTy {base e : Dialect} [DecidableEq base.Ty] [DecidableEq e.Ty] :
    DecidableEq (base ⊞ e).Ty :=
  inferInstanceAs (DecidableEq (base.Ty ⊕ e.Ty))

/-!
# Values of the base in the sum

A value of a base's type is a value of the sum's type `.inl t`, and the
other way round. These two maps move a vector of values between the two.
-/

section
variable {base e : Dialect} [TyDenote base.Ty] [TyDenote e.Ty]

/-- A vector of values of the base's types, as values of the sum's types. -/
def HVector.toSum : {ts : List base.Ty} → HVector toType ts →
    HVector (toType (Ty := (base ⊞ e).Ty)) (ts.map .inl)
  | [], .nil => .nil
  | _ :: _, .cons x xs => .cons x (HVector.toSum xs)

/-- A vector of values of the sum's types `.inl t`, as values of the base's
types. -/
def HVector.ofSum : {ts : List base.Ty} → HVector (toType (Ty := (base ⊞ e).Ty)) (ts.map .inl) →
    HVector toType ts
  | [], .nil => .nil
  | _ :: _, .cons x xs => .cons x (HVector.ofSum xs)

end

/-!
# Contexts and views

What each side of a sum sees of a context of the sum.
-/

namespace Dialect.sum

variable {base e : Dialect}

/-- The type of a function, as the base sees it: it is the base's only when
all its types are. -/
def baseFuncType (t : FuncType (base ⊞ e)) : Option (FuncType base) := do
  let ps ← t.params.mapM Sum.getLeft?
  let rs ← t.results.mapM Sum.getLeft?
  pure ⟨ps, rs⟩

/-- The symbol table of a sum, as the base sees it: the symbols whose types
are all the base's. -/
def baseSymbols (s : Name → Option (FuncType (base ⊞ e))) : Name → Option (FuncType base) :=
  fun g => (s g).bind baseFuncType

/-- The context of an op of the sum, as the base sees it, when the base can
write the function's result types. -/
def baseContext (ctx : OpContext (base ⊞ e)) : Option (OpContext base) :=
  (ctx.results.mapM Sum.getLeft?).map fun rs => ⟨baseSymbols ctx.symbols, rs⟩

/-- The context of an op of the sum, as `e` sees it: all of it. -/
def extContext (ctx : OpContext (base ⊞ e)) : OpContext (base.over e) :=
  ⟨fun g => (ctx.symbols g).map fun t => ⟨t.params, t.results⟩, ctx.results⟩

/-- How the base sees a host that holds the sum: the sum's view, with the
base's ops and types only. -/
def baseView {host : Dialect} (v : DialectView (base ⊞ e) host) : DialectView base host :=
  ⟨fun o => (v.op o).bind Sum.getLeft?, fun t => (v.ty t).bind Sum.getLeft?⟩

/-- How `e` sees a host that holds the sum: the sum's view, with `e`'s ops
only, and every type of the sum. -/
def extView {host : Dialect} (v : DialectView (base ⊞ e) host) : DialectView (base.over e) host :=
  ⟨fun o => (v.op o).bind Sum.getRight?, v.ty⟩

/-- An op of the base obeys its rule in a context of the sum when the base
can write the context's result types and the op obeys the base's rule in
the base's view of the context. -/
def BaseValidOp [DialectValidation base] (ctx : OpContext (base ⊞ e)) (o : base.Op) : Prop :=
  match baseContext ctx with
  | some c => validOp c o
  | none => False

/-- The base's rule for an op in a context of the sum can be decided when
the base's rules can. -/
instance instDecidableBaseValidOp [DialectValidation base] [DecidableDialectValidation base]
    (ctx : OpContext (base ⊞ e))
    (o : base.Op) : Decidable (BaseValidOp ctx o) := by
  unfold BaseValidOp
  split <;> infer_instance

/-!
# The classes of the sum
-/

/-- An op of the sum has the signature that its side gives it. -/
instance instDialectSignature [DialectSignature base] [DialectSignature (base.over e)] :
    DialectSignature (base ⊞ e) where
  sig
    | .inl o => (sig o).map .inl
    | .inr o => sig (d := base.over e) o
  returnTypes
    | .inl o => (returnTypes o).map .inl
    | .inr o => returnTypes (d := base.over e) o
  isTerminator
    | .inl o => isTerminator o
    | .inr o => isTerminator (d := base.over e) o
  succCount
    | .inl o => succCount o
    | .inr o => succCount (d := base.over e) o
  regionKinds
    | .inl o => regionKinds o
    | .inr o => regionKinds (d := base.over e) o

/-- The rule of a region kind in the sum: the base's rule for a kind that the
base registers, and `e`'s for every other kind. -/
def ValidRegion [DialectValidation base] [DialectValidation (base.over e)] {host : Dialect}
    (v : DialectView (base ⊞ e) host) (k : Name) (ctx : FuncContext host) (f : Func host)
    (r : Region host) : Prop :=
  if k ∈ regionKindNames (d := base) then validRegion (d := base) (baseView v) k ctx f r
  else validRegion (d := base.over e) (extView v) k ctx f r

/-- The rule for items in the sum: the base's rule for an item of a kind that
the base registers, and `e`'s for every other kind. -/
def ValidItem [DialectValidation base] [DialectValidation (base.over e)] {host : Dialect}
    (v : DialectView (base ⊞ e) host) (ctx : FuncContext host) (i : DialectItem host) : Prop :=
  if i.kind ∈ itemKindNames (d := base) then validItem (d := base) (baseView v) ctx i
  else validItem (d := base.over e) (extView v) ctx i

/-- The rules of the sum: a type and an op obey the rules of their side, a
function obeys the function rule of each side, and the sum registers the
region kinds and the kinds of item of both sides. -/
instance instDialectValidation [DialectValidation base] [DialectValidation (base.over e)] :
    DialectValidation (base ⊞ e) where
  validTy
    | .inl t => validTy t
    | .inr t => validTy (d := base.over e) (.inr t)
  symbolRefs
    | .inl o => symbolRefs o
    | .inr o => symbolRefs (d := base.over e) o
  validOp ctx
    | .inl o => BaseValidOp ctx o
    | .inr o => validOp (extContext ctx) o
  validFunc v ctx f :=
    validFunc (d := base) (baseView v) ctx f ∧ validFunc (d := base.over e) (extView v) ctx f
  regionKindNames := regionKindNames (d := base) ++ regionKindNames (d := base.over e)
  validRegion := ValidRegion
  itemKindNames := itemKindNames (d := base) ++ itemKindNames (d := base.over e)
  validItem := ValidItem

/-- The sum's rules can be decided when each side's can. -/
instance instDecidableDialectValidation [DialectValidation base] [DialectValidation (base.over e)]
    [DecidableDialectValidation base] [DecidableDialectValidation (base.over e)] :
    DecidableDialectValidation (base ⊞ e) where
  decValidTy
    | .inl t => inferInstanceAs (Decidable (validTy t))
    | .inr t => DecidableDialectValidation.decValidTy (d := base.over e) (.inr t)
  decValidOp ctx
    | .inl o => inferInstanceAs (Decidable (BaseValidOp ctx o))
    | .inr o => DecidableDialectValidation.decValidOp (d := base.over e) (extContext ctx) o
  decValidFunc v ctx f := inferInstanceAs (Decidable (validFunc (d := base) (baseView v) ctx f ∧
    validFunc (d := base.over e) (extView v) ctx f))
  decValidRegion v k ctx f r := by
    show Decidable (ValidRegion v k ctx f r)
    unfold ValidRegion; infer_instance
  decValidItem v ctx i := by
    show Decidable (ValidItem v ctx i)
    unfold ValidItem; infer_instance

/-- The memories of the sum are those of each side, kept apart. An op of the
sum has its side's poison class, and its side's effects on its side's
memories. -/
instance instDialectEffects [h₁ : DialectEffects base] [h₂ : DialectEffects (base.over e)] :
    DialectEffects (base ⊞ e) where
  Mem := h₁.Mem ⊕ h₂.Mem
  poisonClass
    | .inl o => poisonClass o
    | .inr o => poisonClass (d := base.over e) o
  effects
    | .inl o => (effects o).map .inl
    | .inr o => (effects (d := base.over e) o).map .inr

/-- An op of the sum calls the function that it calls on its side. -/
instance instDialectCall [DialectCall base] [DialectCall (base.over e)] :
    DialectCall (base ⊞ e) where
  callee?
    | .inl o => callee? o
    | .inr o => callee? (d := base.over e) o

/-- An op of the sum runs by its side's rule. An op of the base takes its
operands as values of the base's types, and its results become values of
the sum's types. -/
instance instDialectDenote [TyDenote base.Ty] [TyDenote e.Ty] [DialectSignature base]
    [DialectSignature (base.over e)] {m : Type → Type} [Functor m] [DialectDenote base m]
    [DialectDenote (base.over e) m] : DialectDenote (base ⊞ e) m where
  denote
    | .inl o, args => HVector.toSum <$> DialectDenote.denote o (HVector.ofSum args)
    | .inr o, args => DialectDenote.denote (d := base.over e) o args
  exit
    | .inl o, args => DialectDenote.exit o (HVector.ofSum args)
    | .inr o, args => DialectDenote.exit (d := base.over e) o args

/-! # Text -/

variable [DialectName e] [DialectText base] [DialectText (base.over e)]

/-- Reads an op of the sum: a name that `e`'s name starts goes to `e`, and
every other name to the base, at the base's types. -/
def decodeOp (n : String) (as : List Attr) (ts rs : List (base.Ty ⊕ e.Ty)) :
    Option (base.Op ⊕ e.Op) :=
  if wordDialect n = some (name e) then (Fir.decodeOp (d := base.over e) n as ts rs).map .inr
  else (ts.mapM Sum.getLeft?).bind fun ts' => (rs.mapM Sum.getLeft?).bind fun rs' =>
    (Fir.decodeOp (d := base) n as ts' rs').map .inl

/-- Reads a type of the sum: a type of `e`'s name goes to `e`, which must
read it as one of its own types, and every other type to the base. -/
def decodeTy (a : Attr) : Option (base.Ty ⊕ e.Ty) :=
  if a.dialect? = some (name e) then
    match Fir.decodeTy (d := base.over e) a with
    | some (.inr t) => some (.inr t)
    | _ => none
  else (Fir.decodeTy (d := base) a).map .inl

/-- The sum writes each op and type as its side writes it. -/
instance instDialectText : DialectText (base ⊞ e) where
  opName
    | .inl o => opName o
    | .inr o => opName (d := base.over e) o
  opAttrs
    | .inl o => opAttrs o
    | .inr o => opAttrs (d := base.over e) o
  decodeOp := decodeOp
  tyAttr
    | .inl t => tyAttr t
    | .inr t => tyAttr (d := base.over e) (.inr t)
  decodeTy := decodeTy

/-- The dialect set of the sum: the base's set and `e`'s name. -/
instance instDialectSet [DialectSet base] : DialectSet (base ⊞ e) := ⟨names base ++ [name e]⟩

end Dialect.sum

end Fir
