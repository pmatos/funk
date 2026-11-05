import Std.Data.TreeMap
import Fir.Execution.Interpreter

/-!
The values that `fir-ref run` has defined, by name (ADR-2026-11-05-0442).
The spec's environment, `Env`, is a list that every op and every jump puts
values in front of, and `Env.value` looks a name up from the front, so an
operand takes time for each value defined after it, and in a loop the list
grows with the steps run (#47). `Bindings` gives every name the value that
the spec's list gives it, in two parts:

* `young`, a list of the latest values, the latest first, as in the spec.
  Binds put values in front of it, as the spec does, so a run whose ops
  read recent values costs what it costs on the spec's list.
* `old`, a persistent map that binds each name once.

A lookup searches `young`, then `old`. It passes the first `free` entries
of `young` for nothing; past those, the entries it passes are a debt, and
when the debt exceeds `rent` times the length of `young`, `young` moves
into `old` (`settle`). So a run pays to move a value into `old` only after
lookups have passed it about `rent` times, and the time that all lookups
take is linear in the number of values bound and lookups made, whoever
defined what. `rent` and `free` are how `fir-ref` spends its time, not
rules of fir: any values give the same results.

`get` says what bindings give each name, `Agrees` that they give every name
what a spec environment gives it, and `toEnv` is such an environment.
`FirRef.BindingsSteps` proves that each operation here gives what the
spec's gives.
-/

namespace FirRef

open Fir

/-- The values a run has defined, by name: `young`, the latest first, in
front of `old`, which binds each name once. -/
structure Bindings (d : Dialect) [TyDenote d.Ty] where
  /-- The latest values, the latest first. -/
  young : List (Name × DVal d)
  /-- The length of `young`. -/
  count : Nat
  /-- The entries of `young` that lookups have passed, past the first
  `free` of each, since `young` last moved into `old`. -/
  debt : Nat
  /-- One value for each name, older than those of `young`. -/
  old : Std.TreeMap Name (DVal d) compare

namespace Bindings

variable {d : Dialect} [TyDenote d.Ty]

/-- The bindings of a spec environment. -/
def ofEnv (env : Env d) : Bindings d := ⟨env, env.length, 0, ∅⟩

/-- How many entries of `young` lookups may pass, for each entry, before
`young` moves into `old`. -/
def rent : Nat := 32

/-- How many entries of `young` a lookup passes for free. -/
def free : Nat := 8

/-- `young` moved into `old`. -/
def settle (b : Bindings d) : Bindings d :=
  ⟨[], 0, 0, b.young.foldr (fun p m => m.insert p.1 p.2) b.old⟩

/-- The value of `x` in `l`, and `k` plus the entries before it. -/
def find (x : @& Name) : @& List (Name × DVal d) → Nat → Option (DVal d) × Nat
  | [], k => (none, k)
  | (y, v) :: l, k => if x == y then (some v, k) else find x l (k + 1)

/-- The value of `x` among the first `n` entries of `l`, if it is there. -/
def near (x : @& Name) : @& List (Name × DVal d) → Nat → Option (DVal d)
  | [], _ => none
  | _, 0 => none
  | (y, v) :: l, n + 1 => if x == y then some v else near x l n

/-- `b` after a lookup passed `k` entries of `young`. -/
@[inline] def pay (b : Bindings d) (k : Nat) : Bindings d :=
  if k ≤ free then b
  else if rent * b.count < b.debt + k then b.settle else { b with debt := b.debt + k }

/-- The value of the name `x`: its latest definition. -/
@[inline] def value (b : Bindings d) (x : Name) : Except Stuck (DVal d × Bindings d) :=
  match find x b.young 0 with
  | (some v, k) => pure (v, b.pay k)
  | (none, k) => match b.old[x]? with
    | some v => pure (v, b.pay k)
    | none => stuck s!"%{x} is not defined"

/-- The names of `rs` bound to the values `vs`, in reverse, in front of
`acc`, if they have the same length. -/
def zipRev : List (Name × d.Ty) → List (DVal d) → List (Name × DVal d) →
    Option (List (Name × DVal d))
  | [], [], acc => some acc
  | (x, _) :: rs, v :: vs, acc => zipRev rs vs ((x, v) :: acc)
  | _, _, _ => none

/-- Binds the names of `rs` to values, one each, or is stuck for `why`. -/
@[inline] def bind (b : Bindings d) (rs : List (Name × d.Ty)) (vs : List (DVal d)) (why : String) :
    Except Stuck (Bindings d) :=
  match zipRev rs vs [] with
  | some acc => pure { b with young := acc.reverseAux b.young, count := b.count + rs.length }
  | none => stuck why

/-- The results `rs` of an op bound to the values `vs`, in reverse, in front
of `acc`, if they have the same length. -/
def zipRevH : List (Name × d.Ty) → {ts : List d.Ty} → HVector toType ts →
    List (Name × DVal d) → Option (List (Name × DVal d))
  | [], [], .nil, acc => some acc
  | (x, _) :: rs, t :: _, .cons v vs, acc => zipRevH rs vs ((x, ⟨t, v⟩) :: acc)
  | _, _, _, _ => none

/-- Binds the results `rs` of an op to the values `vs`, or is stuck. -/
@[inline] def bindResults (b : Bindings d) (rs : List (Name × d.Ty)) {ts : List d.Ty}
    (vs : HVector toType ts) (why : String) : Except Stuck (Bindings d) :=
  match zipRevH rs vs [] with
  | some acc => pure { b with young := acc.reverseAux b.young, count := b.count + rs.length }
  | none => stuck why

variable [DecidableEq d.Ty]

/-- The values of the names `xs`, one for each type of `ts`. -/
def operands (b : Bindings d) : (ts : List d.Ty) → List Name →
    Except Stuck (HVector toType ts × Bindings d)
  | [], [] => pure (.nil, b)
  | t :: ts, x :: xs => do
    let (⟨t', v⟩, b) ← b.value x
    if h : t' = t then
      let (vs, b) ← b.operands ts xs
      pure (.cons (h ▸ v) vs, b)
    else stuck s!"%{x} does not have the operand's type"
  | _, _ => stuck "an op has a number of operands other than its op instance takes"

/-- The values of the names `xs`, one for each type of `ts`, when each is
among the first entries of `young`. -/
def nearOperands (b : @& Bindings d) : (ts : List d.Ty) → List Name → Option (HVector toType ts)
  | [], [] => some .nil
  | t :: ts, x :: xs => match near x b.young free with
    | some ⟨t', v⟩ =>
      if h : t' = t then match nearOperands b ts xs with
        | some vs => some (.cons (h ▸ v) vs)
        | none => none
      else none
    | none => none
  | _, _ => none

/-- `operands`, quicker when each name is among the first entries of
`young`. -/
@[inline] def args (b : Bindings d) (ts : List d.Ty) (xs : List Name) :
    Except Stuck (HVector toType ts × Bindings d) :=
  match nearOperands b ts xs with
  | some vs => pure (vs, b)
  | none => b.operands ts xs

/-- The values of the names `xs`, after `acc`, the last first. -/
def values (b : Bindings d) : List Name → List (DVal d) → Except Stuck (List (DVal d) × Bindings d)
  | [], acc => pure (acc.reverse, b)
  | x :: xs, acc => match b.value x with
    | .ok (v, b) => values b xs (v :: acc)
    | .error e => .error e

/-- `Func.jump`, on bindings. -/
def jump (f : Func d) (b : Bindings d) (succs : List Succ) (i : Nat) :
    Except Stuck (Block d × Bindings d) := do
  let some s := succs[i]? | stuck s!"the terminator has no successor {i}"
  let some blk := f.block? s.label | stuck s!"^{s.label} is not a block of the function"
  let (vs, b) ← b.values s.args []
  let b' ← b.bind blk.params vs
    s!"^{s.label} takes a number of arguments other than its successor passes"
  if vs.map (·.1) = blk.params.map (·.2) then pure (blk, b')
  else stuck s!"^{s.label} takes arguments of types other than its successor passes"

/-- The parameters `ps` bound to the values `vs`, in reverse, in front of
`acc`, if `vs` has their types. -/
def zipParams : List (Name × d.Ty) → {ts : List d.Ty} → HVector toType ts →
    List (Name × DVal d) → Option (List (Name × DVal d))
  | [], [], .nil, acc => some acc
  | (x, p) :: ps, t :: _, .cons v vs, acc =>
    if p = t then zipParams ps vs ((x, ⟨t, v⟩) :: acc) else none
  | _, _, _, _ => none

/-- `Func.enter`, on bindings. -/
@[inline] def enter (f : Func d) {ts : List d.Ty} (args : HVector toType ts) :
    Except Stuck (List (Operation d) × Bindings d) :=
  match f.blocks.head? with
  | none => stuck "the function has no blocks"
  | some entry =>
    if !entry.params.isEmpty then stuck s!"the entry block ^{entry.label} declares arguments"
    else match zipParams f.params args [] with
      | some acc => pure (entry.body, ⟨acc.reverse, f.params.length, 0, ∅⟩)
      | none => stuck s!"a call passes @{f.name} arguments of types other than its parameter types"

/-! # Bindings stand for a spec environment -/

section Meaning

variable {d : Dialect} [TyDenote d.Ty]

/-- What `b` binds the name `x` to: its latest value in `young`, or else its
value in `old`. -/
def get (b : Bindings d) (x : Name) : Option (DVal d) := (b.young.lookup x).or b.old[x]?

/-- `b` gives every name what the spec environment `env` gives it. -/
def Agrees (b : Bindings d) (env : Env d) : Prop := ∀ x, b.get x = env.lookup x

/-- A spec environment that gives every name what `b` gives it. -/
def toEnv (b : Bindings d) : Env d := b.young ++ b.old.toList

theorem lookup_of_mem {x : Name} {v : DVal d} : ∀ {l : List (Name × DVal d)},
    l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) → (x, v) ∈ l → l.lookup x = some v
  | (y, w) :: l, hp, hm => by
    rw [List.pairwise_cons] at hp
    by_cases hxy : x = y
    · subst hxy
      simp only [List.lookup, beq_self_eq_true]
      rcases List.mem_cons.1 hm with h | h
      · cases h; rfl
      · exact absurd (Std.LawfulEqCmp.compare_eq_iff_eq.2 rfl) (hp.1 (x, v) h)
    · have hb : (x == y) = false := beq_false_of_ne hxy
      simp only [List.lookup, hb]
      rcases List.mem_cons.1 hm with h | h
      · cases h; exact absurd rfl hxy
      · exact lookup_of_mem hp.2 h

theorem lookup_toList (m : Std.TreeMap Name (DVal d) compare) (x : Name) :
    m.toList.lookup x = m[x]? := by
  cases h : m[x]? with
  | none =>
    rw [List.lookup_eq_none_iff]
    rintro ⟨y, w⟩ hp
    have hy : m[y]? = some w := Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 hp
    rw [bne_iff_ne, ne_eq]
    rintro rfl
    rw [h] at hy
    cases hy
  | some v =>
    exact lookup_of_mem Std.TreeMap.distinct_keys_toList
      (Std.TreeMap.mem_toList_iff_getElem?_eq_some.2 h)

theorem lookup_toEnv (b : Bindings d) (x : Name) : b.toEnv.lookup x = b.get x := by
  rw [toEnv, List.lookup_append, lookup_toList]; rfl

theorem agrees_toEnv (b : Bindings d) : Agrees b b.toEnv := fun x => (lookup_toEnv b x).symm

theorem agrees_ofEnv (env : Env d) : Agrees (ofEnv env) env := fun x => by
  simp [get, ofEnv]

theorem find_fst (x : Name) : ∀ (l : List (Name × DVal d)) (k : Nat), (find x l k).1 = l.lookup x
  | [], _ => rfl
  | (y, v) :: l, k => by
    simp only [find, List.lookup]
    cases x == y with
    | true => rfl
    | false => exact find_fst x l (k + 1)

theorem near_some (x : Name) {v : DVal d} :
    ∀ (l : List (Name × DVal d)) (n : Nat), near x l n = some v → l.lookup x = some v
  | [], _, h => by simp [near] at h
  | _ :: _, 0, h => by simp [near] at h
  | (y, w) :: l, n + 1, h => by
    simp only [near] at h
    simp only [List.lookup]
    cases hb : x == y with
    | true => simp only [hb, ite_true] at h ⊢; exact h
    | false => simp only [hb] at h ⊢; exact near_some x l n h

theorem get_foldr (x : Name) (m : Std.TreeMap Name (DVal d) compare) :
    ∀ l : List (Name × DVal d),
      (l.foldr (fun p m => m.insert p.1 p.2) m)[x]? = (l.lookup x).or m[x]?
  | [] => rfl
  | (y, v) :: l => by
    rw [List.foldr_cons, Std.TreeMap.getElem?_insert, get_foldr x m l]
    by_cases hxy : x = y
    · subst hxy
      simp [List.lookup]
    · have hc : ¬ compare y x = .eq := fun hc => hxy (Std.LawfulEqCmp.compare_eq_iff_eq.1 hc).symm
      simp [hc, List.lookup, beq_false_of_ne hxy]

theorem get_settle (b : Bindings d) (x : Name) : b.settle.get x = b.get x := by
  simp only [settle, get, List.lookup_nil, Option.none_or]
  exact get_foldr x b.old b.young

theorem get_pay (b : Bindings d) (k : Nat) (x : Name) : (b.pay k).get x = b.get x := by
  unfold pay
  split
  · rfl
  · split
    · exact get_settle b x
    · rfl

end Meaning

end Bindings

end FirRef
