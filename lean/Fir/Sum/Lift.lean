import Fir.Sum.Inclusion

/-!
An extension `e` written over the dialects it depends on, `dep`, states its
classes for `dep.over e`. To add `e` to a sum `big` that holds `dep` and
more, `big ⊞ e` needs `e`'s classes for `big.over e`. The _lift_ of `e` by
an inclusion `ι` of `dep`'s types in `big`'s gives them, from `e`'s own
classes and `big`'s (ADR-2026-11-09-2306). So two extensions written over
the core combine: `core ⊞ a ⊞ b.lift core ι μ`, where `ι` includes the
core's types in those of `core ⊞ a`, and `μ` names the core's memories as
`core ⊞ a` names them.

The lift `e.lift dep ι μ` has `e`'s ops, `e`'s own types and `e`'s name. It
records `dep`, `ι` and the _memory map_ `μ`, which gives each memory of
`dep` its name in `big`, so that instance search finds them. Over `big`, it
has:

* the signature of each op of `e`, with each type of `dep` included in
  `big`'s;
* `e`'s text for its ops and own types, and `big`'s text for `big`'s types.
  Reading an op projects its operand and result types to `dep`'s, and reads
  it with `e`; a type of `e`'s name goes to `e`, which must read it as one of
  its own, and every other type to `big`;
* `big`'s rule for `big`'s types and `e`'s for its own. An op of `e` sees the
  context only when `e` can write it: the symbols whose types are all `dep`'s
  or `e`'s own, and the function's result types when they all are. In a
  function whose result types `e` cannot write, no op of `e` is valid. This
  is the rule of ADR-2026-11-09-2353, with `e` in place of the base;
* `e`'s function rule, through a view that projects the types to `dep`'s and
  `e`'s own, `e`'s region kinds with their rules, and `e`'s kinds of item
  with its rule for them, through the same view;
* `e`'s poison classes, effects, calls and semantics. An op of `e` takes its
  operands moved down to `dep`'s types and its results move up to `big`'s;
* the memories of `big` and `e`'s own. A name of `e` for a memory of `dep`
  becomes that memory's name in `big`, by `μ`, and a name of one of `e`'s
  own stays as it is. So an op of `e` names each memory of `dep` as `big`
  does, and a memory has one name in the sum `big ⊞ e.lift dep ι μ`.

This section gives, in order: the lift and the inclusion of its types, then
each class of the lift over `big`. The sections after it prove that the lift
of a lawful extension is lawful, for its text, for poison and for its
effects.
-/

namespace Fir

/-!
# The lift
-/

/-- The extension `e`, written over `dep`, lifted by the inclusion `ι` of
`dep`'s types in a larger base's, and the map `μ` of `dep`'s memories to the
larger base's: `e`'s ops and `e`'s own types. -/
def Dialect.lift (e dep : Dialect) {B : Type} [TyDenote dep.Ty] [TyDenote B]
    (_ι : TyIncl dep.Ty B) {MA MB : Type} (_μ : MA → MB) : Dialect :=
  ⟨e.Op, e.Ty⟩

namespace Dialect.lift

variable {e dep big : Dialect} [TyDenote dep.Ty] [TyDenote big.Ty] {ι : TyIncl dep.Ty big.Ty}
  {MA MB : Type} {μ : MA → MB}

/-- A lift has `e`'s name. -/
instance instDialectName [DialectName e] : DialectName (e.lift dep ι μ) := ⟨name e⟩

/-- A lift's own types mean what `e`'s do. -/
instance instTyDenote [TyDenote e.Ty] : TyDenote (e.lift dep ι μ).Ty :=
  inferInstanceAs (TyDenote e.Ty)

instance instTyPoison [TyDenote e.Ty] [TyPoison e.Ty] : TyPoison (e.lift dep ι μ).Ty :=
  inferInstanceAs (TyPoison e.Ty)

instance instTyRefinement [TyDenote e.Ty] [TyRefinement e.Ty] : TyRefinement (e.lift dep ι μ).Ty :=
  inferInstanceAs (TyRefinement e.Ty)

/-- A lift's ops and types compare as `e`'s do. -/
instance instDecidableEqOp [DecidableEq e.Op] : DecidableEq (e.lift dep ι μ).Op :=
  inferInstanceAs (DecidableEq e.Op)

instance instDecidableEqTy [DecidableEq e.Ty] : DecidableEq (e.lift dep ι μ).Ty :=
  inferInstanceAs (DecidableEq e.Ty)

variable [TyDenote e.Ty]

variable (e ι μ) in
/-- The types of `e` over `dep` are included in those of the lift over
`big`: `dep`'s by `ι`, and `e`'s own as they are. -/
abbrev incl : TyIncl (dep.over e).Ty (big.over (e.lift dep ι μ)).Ty := ι.over

/-!
# Contexts and views
-/

/-- The type of a function, as `e` sees it: it is `e`'s only when all its
types are `dep`'s or `e`'s own. -/
def projFuncType (t : FuncType (big.over (e.lift dep ι μ))) : Option (FuncType (dep.over e)) := do
  let ps ← t.params.mapM (incl e ι μ).proj
  let rs ← t.results.mapM (incl e ι μ).proj
  pure ⟨ps, rs⟩

/-- The context of an op of the lift, as `e` sees it, when `e` can write
the function's result types: the symbols whose types `e` can write. -/
def projContext (ctx : OpContext (big.over (e.lift dep ι μ))) : Option (OpContext (dep.over e)) :=
  (ctx.results.mapM (incl e ι μ).proj).map fun rs =>
    ⟨fun g => (ctx.symbols g).bind projFuncType, rs⟩

/-- How `e` sees a host that holds the lift: the lift's view, with the
types projected to `dep`'s and `e`'s own. -/
def projView {host : Dialect} (v : DialectView (big.over (e.lift dep ι μ)) host) :
    DialectView (dep.over e) host :=
  ⟨v.op, fun t => (v.ty t).bind (incl e ι μ).proj⟩

/-- An op of `e` obeys its rule in a context of the lift when `e` can write
the context and the op obeys `e`'s rule there. -/
def ValidOp [DialectValidation (dep.over e)] (ctx : OpContext (big.over (e.lift dep ι μ)))
    (o : e.Op) : Prop :=
  match projContext ctx with
  | some c => validOp c o
  | none => False

/-- `e`'s rule for an op in a context of the lift can be decided when `e`'s
rules can. -/
instance instDecidableValidOp [DialectValidation (dep.over e)]
    [DecidableDialectValidation (dep.over e)] (ctx : OpContext (big.over (e.lift dep ι μ)))
    (o : e.Op) : Decidable (ValidOp ctx o) := by
  unfold ValidOp
  split <;> infer_instance

/-!
# The classes of the lift
-/

/-- An op of the lift has `e`'s signature, with `dep`'s types included in
`big`'s, and the region kinds that `e` gives it. -/
instance instDialectSignature [DialectSignature (dep.over e)] :
    DialectSignature (big.over (e.lift dep ι μ)) where
  sig o := (sig (d := dep.over e) o).map (incl e ι μ).incl
  returnTypes o := (returnTypes (d := dep.over e) o).map (incl e ι μ).incl
  isTerminator o := isTerminator (d := dep.over e) o
  succCount o := succCount (d := dep.over e) o
  regionKinds o := regionKinds (d := dep.over e) o

/-- The rules of the lift: `big`'s for `big`'s types, `e`'s for its own
types and its ops, and `e`'s function rule, region kinds and kinds of item
through its
view. -/
instance instDialectValidation [DialectValidation big] [DialectValidation (dep.over e)] :
    DialectValidation (big.over (e.lift dep ι μ)) where
  validTy
    | .inl t => validTy t
    | .inr t => validTy (d := dep.over e) (.inr t)
  symbolRefs o := symbolRefs (d := dep.over e) o
  validOp := ValidOp
  validFunc v ctx f := validFunc (d := dep.over e) (projView v) ctx f
  regionKindNames := regionKindNames (d := dep.over e)
  validRegion v k ctx f r := validRegion (d := dep.over e) (projView v) k ctx f r
  itemKindNames := itemKindNames (d := dep.over e)
  validItem v ctx i := validItem (d := dep.over e) (projView v) ctx i

/-- The lift's rules can be decided when `big`'s and `e`'s can. -/
instance instDecidableDialectValidation [DialectValidation big] [DialectValidation (dep.over e)]
    [DecidableDialectValidation big] [DecidableDialectValidation (dep.over e)] :
    DecidableDialectValidation (big.over (e.lift dep ι μ)) where
  decValidTy
    | .inl t => inferInstanceAs (Decidable (validTy t))
    | .inr t => DecidableDialectValidation.decValidTy (d := dep.over e) (.inr t)
  decValidOp ctx o := instDecidableValidOp (e := e) ctx o
  decValidFunc v ctx f := DecidableDialectValidation.decValidFunc (d := dep.over e) (projView v) ctx f
  decValidRegion v k ctx f r :=
    DecidableDialectValidation.decValidRegion (d := dep.over e) (projView v) k ctx f r
  decValidItem v ctx i :=
    DecidableDialectValidation.decValidItem (d := dep.over e) (projView v) ctx i

section
variable [DialectEffects dep] [DialectEffects big] [DialectEffects (dep.over e)]
  [DialectMemOver dep e]

/-- The memory map of the lift: a memory of `dep` that `e` names gets its
name in `big`, by `μ`, and one of `e`'s own keeps its name. -/
def liftMem (μ : DialectEffects.Mem dep → DialectEffects.Mem big)
    (x : DialectEffects.Mem (dep.over e)) : DialectEffects.Mem big ⊕ DialectMemOver.Own dep e :=
  match DialectMemOver.split x with
  | .inl a => .inl (μ a)
  | .inr o => .inr o

omit [TyDenote dep.Ty] [TyDenote big.Ty] [TyDenote e.Ty] in
/-- `e`'s name for a memory of `dep` becomes the memory's name in `big`. -/
theorem liftMem_ofBase (μ : DialectEffects.Mem dep → DialectEffects.Mem big)
    (a : DialectEffects.Mem dep) : liftMem (e := e) μ (DialectMemOver.ofBase a) = .inl (μ a) := by
  simp [liftMem, DialectMemOver.ofBase, DialectMemOver.split_join]

/-- The memories of the lift are `big`'s and `e`'s own. An op of the lift
has `e`'s poison class, and `e`'s effects with their memories mapped by the
lift's memory map. -/
instance instDialectEffects {μ : DialectEffects.Mem dep → DialectEffects.Mem big} :
    DialectEffects (big.over (e.lift dep ι μ)) :=
  ⟨DialectEffects.Mem big ⊕ DialectMemOver.Own dep e, fun o => poisonClass (d := dep.over e) o,
    fun o => (effects (d := dep.over e) o).map (liftMem μ)⟩

/-- The memories of the lift over `big` are `big`'s and `e`'s own. -/
instance instDialectMemOver {μ : DialectEffects.Mem dep → DialectEffects.Mem big} :
    DialectMemOver big (e.lift dep ι μ) :=
  ⟨DialectMemOver.Own dep e, id, id, fun _ => rfl, fun _ => rfl⟩

end

/-- An op of the lift calls what it calls in `e`. -/
instance instDialectCall [DialectCall (dep.over e)] : DialectCall (big.over (e.lift dep ι μ)) :=
  ⟨fun o => callee? (d := dep.over e) o⟩

/-- An op of the lift runs by `e`'s rule: it takes its operands moved down
to `dep`'s types, and its results move up to `big`'s. -/
instance instDialectDenote [DialectSignature (dep.over e)] {m : Type → Type} [Functor m]
    [DialectDenote (dep.over e) m] : DialectDenote (big.over (e.lift dep ι μ)) m where
  denote o args := HVector.up (incl e ι μ) <$>
    DialectDenote.denote (d := dep.over e) o (HVector.down (incl e ι μ) args)
  exit o args := DialectDenote.exit (d := dep.over e) o (HVector.down (incl e ι μ) args)

/-! # Text -/

variable [DialectName e] [DialectText big] [DialectText (dep.over e)]

variable (ι) in
/-- Reads an op of the lift: its operand and result types projected to
`dep`'s and `e`'s own, read by `e`. -/
def decodeOp (n : String) (as : List Attr) (ts rs : List (big.over (e.lift dep ι μ)).Ty) :
    Option e.Op :=
  (ts.mapM (incl e ι μ).proj).bind fun ts' => (rs.mapM (incl e ι μ).proj).bind fun rs' =>
    Fir.decodeOp (d := dep.over e) n as ts' rs'

variable (dep) in
/-- Writes a type of the lift: `big`'s as `big` does, and `e`'s own as `e`
does. -/
def tyAttr : big.Ty ⊕ e.Ty → Attr
  | .inl t => Fir.tyAttr t
  | .inr t => Fir.tyAttr (d := dep.over e) (.inr t)

variable (dep) in
/-- Reads a type of the lift: a type of `e`'s name goes to `e`, which must
read it as one of its own types, and every other type to `big`. -/
def decodeTy (a : Attr) : Option (big.Ty ⊕ e.Ty) :=
  if a.dialect? = some (name e) then
    match Fir.decodeTy (d := dep.over e) a with
    | some (.inr t) => some (.inr t)
    | _ => none
  else (Fir.decodeTy (d := big) a).map .inl

/-- The lift writes its ops as `e` does, and its types as their side does. -/
instance instDialectText : DialectText (big.over (e.lift dep ι μ)) where
  opName o := opName (d := dep.over e) o
  opAttrs o := opAttrs (d := dep.over e) o
  decodeOp := decodeOp (e := e) ι
  tyAttr := tyAttr (e := e) dep
  decodeTy := decodeTy (e := e) dep

end Dialect.lift

end Fir
