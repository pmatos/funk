import Fir.Sum.Dialect
import Fir.Core.Signature

/-!
The second dialect in tree, `gpu`, is shaped like a GPU kernel language
(ADR-2026-11-09-1545). A host module holds a nested device module whose
dialect set names `gpu`, and the kernels are the functions of that device
module. In M1 a kernel runs one work-item at a time, with the work-item's
ids given as inputs: no op of `gpu` needs another work-item, so barriers are
left out.

The dialect extends the core: its ops give the core's integers, which it
names as its base's types, and it has no types of its own. Its own word is
the _dimension_ attribute, `gpu.x`, `gpu.y` or `gpu.z`, which picks one of
the three dimensions of the grid of work-items. Each op asks the work-item
one question in one dimension and gives the answer as an `i32`:

* `%i: i32 = gpu.work_item_id gpu.x` is the work-item's id within its
  work-group;
* `%g: i32 = gpu.work_group_id gpu.x` is the id of its work-group;
* `%s: i32 = gpu.work_group_size gpu.x` is the number of work-items in a
  work-group;
* `%n: i32 = gpu.num_work_groups gpu.x` is the number of work-groups.

This section gives the dialect's abstract syntax and signature; its text,
its rules and its effects follow in sections of their own. Its execution
rules come with the runs of a work-item (#212, stage 2).
-/

namespace Fir.Gpu

/-- A dimension of the grid of work-items: `gpu.x`, `gpu.y` or `gpu.z`. -/
inductive Dim where
  | x
  | y
  | z
  deriving Repr, DecidableEq

/-- What an op asks of the work-item that runs it. -/
inductive Query where
  /-- The work-item's id within its work-group. -/
  | workItemId
  /-- The id of the work-item's work-group. -/
  | workGroupId
  /-- The number of work-items in a work-group. -/
  | workGroupSize
  /-- The number of work-groups. -/
  | numWorkGroups
  deriving Repr, DecidableEq

/-- An op instance of the dialect: `query q d w` asks the question `q` in
the dimension `d`, and gives the answer as an `iN` with `N = w`. -/
inductive Op where
  | query (q : Query) (d : Dim) (w : Nat)
  deriving Repr, DecidableEq

end Fir.Gpu

namespace Fir

/-- The dialect `gpu` on its own: its ops, and no types of its own. -/
abbrev GpuExt : Dialect := ⟨Gpu.Op, Empty⟩

/-- Its name, the word before the `.` of each of its words. -/
instance Gpu.instDialectName : DialectName GpuExt := ⟨"gpu"⟩

/-- The dialect `gpu` over the core: its ops, at the core's types. -/
abbrev GpuDialect : Dialect := CoreDialect.over GpuExt

/-- The sum of the core and `gpu`: what `funk` and `fir-ref` read. -/
abbrev CoreGpu : Dialect := CoreDialect ⊞ GpuExt

namespace Gpu

/-- An op of `gpu` takes no operand. -/
def Op.sig : Op → List (Core.Ty ⊕ Empty)
  | .query .. => []

/-- An op of `gpu` gives one integer, of the width of its instance. -/
def Op.returnTypes : Op → List (Core.Ty ⊕ Empty)
  | .query _ _ w => [.inl (.int w)]

/-- No op of `gpu` ends a block, has a successor or owns a region. -/
instance instDialectSignature : DialectSignature GpuDialect where
  sig := Op.sig
  returnTypes := Op.returnTypes
  isTerminator _ := false
  succCount _ := 0

end Gpu

end Fir
