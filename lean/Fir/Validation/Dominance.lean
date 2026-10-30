import Fir.Validation.Scope

/-!
fir is in SSA form: every value has one definition, and that definition
dominates each of its uses. Dominance is a property of the function's
control-flow graph, whose nodes are the blocks and whose edges go from a
block to the successors of its terminator.

The graph, reachability and dominance below are over a function's top-level
blocks. How values are scoped in the regions of an op, and how dominance
reaches into them, is left to H6, with the first dialect whose ops have
regions; no core op has one. H6 also reconciles the two views of a function
that validation uses: the top-level blocks here, and every block at any
depth for names and their types.

# The control-flow graph
-/

namespace Fir

variable {d : Dialect}

/-- The labels of the blocks that block `b` can jump to. -/
def Block.succLabels (b : Block d) : List Name :=
  b.body.flatMap fun o => o.succs.map (·.label)

/-- An edge of the control-flow graph, from the block labelled `a` to the
block labelled `b`. -/
def Func.Edge (f : Func d) (a b : Name) : Prop :=
  ∃ blk ∈ f.blocks, blk.label = a ∧ b ∈ blk.succLabels

/-- The label of the function's entry block, the first of its body. -/
def Func.entryLabel? (f : Func d) : Option Name :=
  f.blocks.head?.map (·.label)

/--
`f.Reachable l` holds when some path through the graph goes from the entry
block to the block labelled `l`. The entry is reachable.
-/
inductive Func.Reachable (f : Func d) : Name → Prop
  | entry {e : Name} : f.entryLabel? = some e → f.Reachable e
  | step {x y : Name} : f.Reachable x → f.Edge x y → f.Reachable y

/--
`f.ReachesAvoiding a l` holds when some path through the graph goes from the
entry block to the block labelled `l` without passing through the block
labelled `a`.
-/
inductive Func.ReachesAvoiding (f : Func d) (a : Name) : Name → Prop
  | entry {e : Name} : f.entryLabel? = some e → e ≠ a → f.ReachesAvoiding a e
  | step {x y : Name} : f.ReachesAvoiding a x → f.Edge x y → y ≠ a →
      f.ReachesAvoiding a y

/-!
# Dominance

Every block of a valid function is reachable from its entry
(ADR-2026-10-30-0817). This is stricter than LLVM, which accepts blocks that
the entry cannot reach. Producers, frontends and passes alike, delete such
blocks before validation.

So dominance has its standard meaning everywhere. A block `a` dominates a
block `b` when every path from the entry to `b` passes through `a`.
Equivalently, `b` cannot be reached once `a` is removed. Every block
dominates itself, and the entry dominates every block. Since every block is
reachable, every use has a path from the entry through its definition, and
no group of blocks can define values in a cycle, each using the other's.
-/

/-- Block `a` dominates block `b`. -/
def Func.Dominates (f : Func d) (a b : Name) : Prop :=
  a = b ∨ ¬ f.ReachesAvoiding a b

/-- Where a value is defined: a parameter of the function, an argument of a
block, or a result of the op at an index of a block. -/
inductive DefSite where
  | param
  | arg (block : Name)
  | result (block : Name) (index : Nat)

/-- The function defines the value `x` at a site. -/
def Func.Defines (f : Func d) (x : Name) : DefSite → Prop
  | .param => x ∈ f.params.map (·.1)
  | .arg l => ∃ b ∈ f.blocks, b.label = l ∧ x ∈ b.params.map (·.1)
  | .result l j => ∃ b ∈ f.blocks, b.label = l ∧
      ∃ o, b.body[j]? = some o ∧ x ∈ o.results.map (·.1)

/--
A definition at site `s` dominates a use by the op at index `i` of the block
labelled `l`. A parameter dominates every use. A block argument dominates the
uses in every block its block dominates, its own included. An op's result
dominates the uses by later ops of its block, and the uses in the blocks that
its block dominates. An op never uses its own results.

The arguments that a terminator passes to its successors are uses by the
terminator, in its own block.
-/
def Func.DominatesUse (f : Func d) (s : DefSite) (l : Name) (i : Nat) : Prop :=
  match s with
  | .param => True
  | .arg a => f.Dominates a l
  | .result a j => (a = l ∧ j < i) ∨ (a ≠ l ∧ f.Dominates a l)

/--
A use of `x` by the op at index `i` of block `l` is in scope: the function
defines `x`, and the definition dominates the use. The first half is
isolation from above (H2): a function uses only values it defines itself.
-/
def Func.InScope (f : Func d) (x : Name) (l : Name) (i : Nat) : Prop :=
  (∃ s, f.Defines x s) ∧ ∀ s, f.Defines x s → f.DominatesUse s l i

end Fir
