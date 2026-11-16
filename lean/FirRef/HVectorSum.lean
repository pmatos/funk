import Fir.Sum.Dialect
import FirRef.HVector

/-!
The sum's moves of a vector between the base's types and the sum's,
`HVector.toSum` and `HVector.ofSum`, in loops of tail calls. The spec's take
stack for each value, and the sum of the core and `gpu` moves the operands
of every op of the core and the results of every op that gives any, so a
`ret` of 100,000 values overflowed a 256 KiB stack (#405). `FirRef.Run`
reaches these through `sumDenote`, a copy of the sum's rules compiled after
them: the spec's instance, compiled before any theorem of `FirRef`, still
calls the spec's moves.
-/

namespace FirRef

open Fir

variable {base e : Dialect} [TyDenote base.Ty] [TyDenote e.Ty]

/-- `HVector.toSum` of `xs`, after the values of `acc`, the last first. -/
def toSumTR {ts : List base.Ty} : (rest : List base.Ty) → HVector toType rest →
    (acc : List (DVal (base ⊞ e))) → (acc.map (·.1)).reverse ++ rest.map .inl = ts.map .inl →
    HVector (toType (Ty := (base ⊞ e).Ty)) (ts.map .inl)
  | [], .nil, acc, h => ofRev acc (by rw [← h]; exact (List.append_nil _).symm)
  | t :: _, .cons x xs, acc, h => toSumTR _ xs (⟨.inl t, x⟩ :: acc)
      (by rw [← h, List.map_cons, List.reverse_cons, List.append_assoc]; rfl)

/-- `HVector.ofSum` of `xs`, after the values of `acc`, the last first. -/
def ofSumTR {ts : List base.Ty} : (rest : List base.Ty) →
    HVector (toType (Ty := (base ⊞ e).Ty)) (rest.map .inl) →
    (acc : List (DVal base)) → (acc.map (·.1)).reverse ++ rest = ts → HVector toType ts
  | [], .nil, acc, h => ofRev acc (by simpa using h)
  | t :: _, .cons x xs, acc, h => ofSumTR _ xs (⟨t, x⟩ :: acc) (by simpa using h)

theorem toDVals_toSumTR {ts : List base.Ty} : ∀ (rest : List base.Ty) (xs : HVector toType rest)
    (acc : List (DVal (base ⊞ e))) (h : (acc.map (·.1)).reverse ++ rest.map .inl = ts.map .inl),
    (toSumTR rest xs acc h).toDVals = acc.reverse ++ (HVector.toSum (e := e) xs).toDVals
  | [], .nil, acc, h => by simp [toSumTR, toDVals_ofRev, HVector.toSum, HVector.toDVals]
  | _ :: rest, .cons x xs, acc, h => by
    simp only [toSumTR, toDVals_toSumTR rest xs, HVector.toSum, List.reverse_cons,
      List.append_assoc]
    rfl

theorem toDVals_ofSumTR {ts : List base.Ty} : ∀ (rest : List base.Ty)
    (xs : HVector (toType (Ty := (base ⊞ e).Ty)) (rest.map .inl))
    (acc : List (DVal base)) (h : (acc.map (·.1)).reverse ++ rest = ts),
    (ofSumTR rest xs acc h).toDVals = acc.reverse ++ (HVector.ofSum xs).toDVals
  | [], .nil, acc, h => by simp [ofSumTR, toDVals_ofRev, HVector.ofSum, HVector.toDVals]
  | _ :: rest, .cons x xs, acc, h => by
    simp [ofSumTR, toDVals_ofSumTR rest xs, HVector.ofSum, HVector.toDVals]

/-- `HVector.toSum`, in a loop of tail calls. -/
def toSumFast {ts : List base.Ty} (xs : HVector toType ts) :
    HVector (toType (Ty := (base ⊞ e).Ty)) (ts.map .inl) :=
  toSumTR ts xs [] rfl

/-- `HVector.ofSum`, in a loop of tail calls. -/
def ofSumFast {ts : List base.Ty} (xs : HVector (toType (Ty := (base ⊞ e).Ty)) (ts.map .inl)) :
    HVector toType ts :=
  ofSumTR ts xs [] rfl

@[csimp] theorem toSum_eq_toSumFast : @HVector.toSum = @toSumFast := by
  funext base e _ _ ts xs
  exact toDVals_inj (ws := toSumFast xs)
    ((toDVals_toSumTR ts xs [] rfl).trans (List.nil_append _)).symm

@[csimp] theorem ofSum_eq_ofSumFast : @HVector.ofSum = @ofSumFast := by
  funext base e _ _ ts xs
  exact toDVals_inj (ws := ofSumFast xs)
    ((toDVals_ofSumTR ts xs [] rfl).trans (List.nil_append _)).symm

/-- `Dialect.sum.instDialectDenote`, compiled after `toSum_eq_toSumFast` and
`ofSum_eq_ofSumFast`, so that its moves of vectors are loops. -/
@[instance_reducible] def sumDenote [DialectSignature base] [DialectSignature (base.over e)]
    {m : Type → Type} [Functor m] [DialectDenote base m] [DialectDenote (base.over e) m] :
    DialectDenote (base ⊞ e) m where
  denote
    | .inl o, args => HVector.toSum <$> DialectDenote.denote o (HVector.ofSum args)
    | .inr o, args => DialectDenote.denote (d := base.over e) o args
  exit
    | .inl o, args => DialectDenote.exit o (HVector.ofSum args)
    | .inr o, args => DialectDenote.exit (d := base.over e) o args

theorem sumDenote_eq [DialectSignature base] [DialectSignature (base.over e)]
    {m : Type → Type} [Functor m] [DialectDenote base m] [DialectDenote (base.over e) m] :
    (sumDenote : DialectDenote (base ⊞ e) m) = Dialect.sum.instDialectDenote := rfl

end FirRef
