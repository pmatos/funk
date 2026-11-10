import Fir.Execution.OpEffects
import Fir.Execution.Effects
import Fir.Validation.Scope

/-!
# Function summaries

An op's set of effects holds the effects of its own rule. An op with a
callee runs its callee, so it has its callee's effects too
(ADR-2026-11-02-1514): a call has every effect that some op of its callee
has, or of a function that the callee calls in turn. This section gives
each function of a symbol table its _summary_, the effects that a call of
it may have, and so gives each op in place its effects with its callee's
(ADR-2026-11-10-2108).

* _A join of effect sets._ Two sets of effects join into the set that has
  every effect of either: a memory-named effect touches the memories of
  both, and every other effect is there when it is in either. A set is
  _below_ another when it has no effect that the other leaves out.
* _What a caller sees._ Every effect of an op of a function is an effect
  of a call of it, but control: a terminator of the callee ends a block of
  the callee, not the caller's, so a call is not a terminator for it.
* _The functions a call may reach._ A function reaches itself, and every
  function that an op of a function it reaches calls. The functions it
  reaches are found by a walk that keeps its work in a list, so a long
  chain of calls or a deep recursion takes no stack per call.
* _The summary_ of a function is the join of what a caller sees of each op
  of each function that it reaches, recursion included: a function that
  calls itself reaches nothing new. A call of a symbol that names no
  function of the table has every effect, as nothing narrower is known of
  it (ADR-2026-11-09-1541); validation rejects such a call.
* _The effects of an op in place_ are those of its own rule, and, when it
  calls a function, the callee's summary.

Calls resolve in the symbol table that holds the caller, so the summary is
a summary of a table's function: a module nested in another has a table of
its own (ADR-2026-11-10-1510). The section on function summaries' laws
proves the summary a fixpoint, the least one, and proves it sound: a
function whose summary leaves out an effect does not have it.
-/

namespace Fir

/-! # Joining effect sets -/

section Join

variable {Mem : Type}

/-- A set of memories is below another when the other holds every memory it
holds. -/
def MemSet.Sub (a b : MemSet Mem) : Prop := ∀ m, a.Has m → b.Has m

/-- An effect set is below another when the other has every effect it has:
it touches no memory that the other leaves out, and has no other effect
that the other leaves out. -/
structure Effects.Le (a b : Effects Mem) : Prop where
  reads : a.reads.Sub b.reads
  writes : a.writes.Sub b.writes
  allocates : a.allocates.Sub b.allocates
  mayUB : a.mayUB = true → b.mayUB = true
  mayPoison : a.mayPoison = true → b.mayPoison = true
  observable : a.observable = true → b.observable = true
  control : a.control = true → b.control = true

instance : LE (Effects Mem) := ⟨Effects.Le⟩

/-- The effects of a set as a caller of its op sees them: every effect but
control. -/
def Effects.callerView (e : Effects Mem) : Effects Mem := { e with control := false }

/-- The join of two sets of memories: every memory, if either is, and
otherwise the memories of both. A memory that both list is listed twice: a
set of memories holds what it lists, whatever the order and however often. -/
def MemSet.join : MemSet Mem → MemSet Mem → MemSet Mem
  | .every, _ | .these _, .every => .every
  | .these ms, .these ns => .these (ms ++ ns)

/-- The join of two effect sets: each memory-named effect touches the
memories of both, and every other effect is there when either has it. -/
def Effects.join (a b : Effects Mem) : Effects Mem where
  reads := a.reads.join b.reads
  writes := a.writes.join b.writes
  allocates := a.allocates.join b.allocates
  mayUB := a.mayUB || b.mayUB
  mayPoison := a.mayPoison || b.mayPoison
  observable := a.observable || b.observable
  control := a.control || b.control

/-- The join of a list of effect sets, from the empty set, from the left. -/
def Effects.joinAll (es : List (Effects Mem)) : Effects Mem :=
  es.foldl Effects.join {}

end Join

/-! # The summary of a function -/

variable {d : Dialect} [DialectSignature d] [DialectCall d]

/-- The symbol that an op in place calls: its callee, when it is not a
terminator. The interpreter runs a terminator by its exit, whatever its
callee. -/
def Operation.call? (o : Operation d) : Option Name :=
  if isTerminator o.op then none else callee? o.op

/-- The function of a symbol table that a symbol names: its first function
with that symbol, as the interpreter finds a callee. -/
def SymbolTable.func? (t : SymbolTable d) (s : Name) : Option (Func d) :=
  t.funcs.find? (·.name == s)

/-- The symbols that the ops of `f` call and that name functions of `t`. -/
def SymbolTable.callees (t : SymbolTable d) (f : Func d) : List Name :=
  (f.allOps.filterMap Operation.call?).filter fun s => (t.func? s).isSome

/-- How many functions of `t` are named by no symbol of `seen`. -/
def SymbolTable.unseen (t : SymbolTable d) (seen : List Name) : Nat :=
  (t.funcs.map (·.name)).countP fun s => s ∉ seen

/-- A test that holds of fewer elements, and fails of one that the other
holds of, counts fewer elements of a list that holds that one. -/
theorem countP_lt_of_mem {α : Type} {p q : α → Bool} {a : α} :
    ∀ {l : List α}, (∀ x, q x = true → p x = true) → a ∈ l → p a = true → q a = false →
      l.countP q < l.countP p
  | x :: l, hqp, ha, hpa, hqa => by
    simp only [List.countP_cons]
    have hle : l.countP q ≤ l.countP p := List.countP_mono_left fun y _ => hqp y
    rcases List.mem_cons.1 ha with rfl | ha'
    · simp [hpa, hqa]
      omega
    · have := countP_lt_of_mem hqp ha' hpa hqa
      cases hq : q x
      · cases p x <;> simp <;> omega
      · simp [hqp x hq]
        omega

omit [DialectSignature d] [DialectCall d] in
/-- Leaving one more function seen leaves fewer unseen. -/
theorem SymbolTable.unseen_lt {t : SymbolTable d} {seen : List Name} {s : Name} {f : Func d}
    (hs : s ∉ seen) (hf : t.func? s = some f) : t.unseen (seen ++ [s]) < t.unseen seen :=
  countP_lt_of_mem (fun x h => by simp_all)
    (List.mem_map.2 ⟨f, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩)
    (by simpa using hs) (by simp)

/-- The symbols of the functions of `t` that the run of a function of `work`
may reach, after the functions of `seen`: a walk that takes the first
symbol of `work`, and, unless it is seen or names no function, leaves it
seen and puts its function's callees first in `work`. Each step leaves one
more function seen or shortens `work`, so the walk ends, and it keeps its
work in lists, so it takes no stack per call. -/
def SymbolTable.reach (t : SymbolTable d) (work seen : List Name) : List Name :=
  match work with
  | [] => seen
  | s :: work =>
    if _hs : s ∈ seen then t.reach work seen
    else match _hf : t.func? s with
      | some f => t.reach (t.callees f ++ work) (seen ++ [s])
      | none => t.reach work seen
termination_by (t.unseen seen, work.length)
decreasing_by
  · exact Prod.Lex.right _ (Nat.lt_succ_self _)
  · exact Prod.Lex.left _ _ (SymbolTable.unseen_lt _hs _hf)
  · exact Prod.Lex.right _ (Nat.lt_succ_self _)

variable [DialectEffects d]

/-- What a caller sees of an op of a function of `t`, beside its callee's
summary: the effects of its own rule, and every effect when it calls a
symbol that names no function of `t`. -/
def SymbolTable.opOwn (t : SymbolTable d) (o : Operation d) :
    Effects (DialectEffects.Mem d) :=
  match o.call? with
  | some s => if (t.func? s).isSome then (effects o.op).callerView
    else ((effects o.op).join Effects.all).callerView
  | none => (effects o.op).callerView

/-- What a caller sees of the ops of `f` alone: the join of `t.opOwn` over
every op of `f`. -/
def SymbolTable.funcOwn (t : SymbolTable d) (f : Func d) : Effects (DialectEffects.Mem d) :=
  Effects.joinAll (f.allOps.map t.opOwn)

/-- The summary of the function of `t` that the symbol `s` names: the join
of what a caller sees of the ops of every function that it reaches. A
symbol that names no function of `t` has the empty summary. -/
def SymbolTable.summary (t : SymbolTable d) (s : Name) : Effects (DialectEffects.Mem d) :=
  Effects.joinAll ((t.reach [s] []).filterMap fun g => (t.func? g).map t.funcOwn)

/-- The effects of an op in place in a function of `t`: those of its own
rule, and, when it calls a function, its callee's summary, or every effect
but control when its callee names no function of `t`. -/
def SymbolTable.opEffects (t : SymbolTable d) (o : Operation d) :
    Effects (DialectEffects.Mem d) :=
  match o.call? with
  | some s => (effects o.op).join
    (if (t.func? s).isSome then t.summary s else Effects.all.callerView)
  | none => effects o.op

end Fir
