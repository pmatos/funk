import Fir.Execution.MemoryStepPaths

/-!
# The callee of a call, with memory

A call with memory calls one symbol on some arguments, from some memories,
with the steps the call leaves (`Func.MemCallsAt`): the callee that its op
names, from the memories the op starts with, with the steps the op leaves,
or the symbol that its rule picks (#235), from the memories that the rule
ends with, after one more step, the call's. These facts say how those steps
change with the steps the op leaves, as `Fir.Execution.CallsAt` says in the
set monad.
-/

namespace Fir

open Memory

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (StateT (Memories Mem unit) SetM)]
  {M : Module d} {o : Operation d} {args : HVector toType (sig o.op)} {S S₁ : Memories Mem unit}
  {n n' : Nat} {s : Name} {ts : List d.Ty} {cargs : HVector toType ts}

omit [DecidableEq Mem] in
/-- A call leaves its callee at most the steps that its op leaves, and at
least all but one. -/
theorem Func.MemCallsAt.le (h : Func.MemCallsAt M o args S n s ts cargs n' S₁) :
    n' ≤ n ∧ n ≤ n' + 1 := by
  cases h with
  | fixed => exact ⟨Nat.le_refl _, Nat.le_succ _⟩
  | picked => exact ⟨Nat.le_succ _, Nat.le_refl _⟩

omit [DecidableEq Mem] in
/-- A call with `j` more steps left after its op leaves its callee `j` more. -/
theorem Func.MemCallsAt.up (j : Nat) (h : Func.MemCallsAt M o args S n s ts cargs n' S₁) :
    Func.MemCallsAt M o args S (n + j) s ts cargs (n' + j) S₁ := by
  cases h with
  | fixed hc => exact .fixed hc
  | picked hc hs => rw [Nat.add_right_comm]; exact .picked hc hs

omit [DecidableEq Mem] in
/-- A call with `j` more steps left after its op calls the same symbol on
the same arguments, from the same memories, with `j` fewer steps left for
its callee, unless its callee is picked and its op leaves no step for the
call. -/
theorem Func.MemCallsAt.down {k j : Nat}
    (h : Func.MemCallsAt M o args S (k + j) s ts cargs n' S₁) :
    (∃ n'', n' = n'' + j ∧ Func.MemCallsAt M o args S k s ts cargs n'' S₁) ∨
      (k = 0 ∧ callee? o.op = some .picked ∧
        DialectDenote.pick (m := StateT (Memories Mem unit) SetM) o.op
          (M.callable (sig o.op).tail (returnTypes o.op)) args S (.ok (s, S₁))) := by
  generalize hm : k + j = m at h
  cases h with
  | fixed hc => exact .inl ⟨k, hm.symm, .fixed hc⟩
  | picked hc hs =>
    cases k with
    | zero => exact .inr ⟨rfl, hc, hs⟩
    | succ k => exact .inl ⟨k, by omega, .picked hc hs⟩

omit [DecidableEq Mem] in
/-- A call at one budget calls the same symbol on the same arguments, from
the same memories, at every budget at which its op leaves the call `m`
steps. -/
theorem Func.MemCallsAt.at (h : Func.MemCallsAt M o args S n s ts cargs n' S₁) (m : Nat) :
    Func.MemCallsAt M o args S (m + (n - n')) s ts cargs m S₁ := by
  cases h with
  | fixed hc => rw [Nat.sub_self, Nat.add_zero]; exact .fixed hc
  | picked hc hs => rw [show _ + 1 - _ = 1 by omega]; exact .picked hc hs

omit [DecidableEq Mem] in
/-- A call that leaves its callee fewer steps than its op leaves picks its
callee. -/
theorem Func.MemCallsAt.picked_of_lt (h : Func.MemCallsAt M o args S n s ts cargs n' S₁)
    (hlt : n' < n) : callee? o.op = some .picked ∧
      DialectDenote.pick (m := StateT (Memories Mem unit) SetM) o.op
        (M.callable (sig o.op).tail (returnTypes o.op)) args S (.ok (s, S₁)) := by
  cases h with
  | fixed => exact absurd hlt (Nat.lt_irrefl _)
  | picked hc hs => exact ⟨hc, hs⟩

end Fir
