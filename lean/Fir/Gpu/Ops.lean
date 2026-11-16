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

One more op allocates in work-group memory. Work-group memory is an
ordinary memory of the host's data layout, any memory that it declares,
with no number fixed (the human's ruling of 2026-11-16 on #212):

* `%p: ptr(3) = gpu.work_group_alloca i32 64` allocates room for 64 `i32` in
  the memory of its result, here memory 3, as `alloca` does, and gives the
  pointer to it. What makes the memory work-group memory is this op: its
  allocation lives for the whole run of the kernel, not only until the call
  that made it returns. The core's `ptr(N)`, `alloca`, `load`, `store` and
  `ptradd` work on the memory unchanged.

This section gives the dialect's abstract syntax and signature; its text,
its rules, its effects and its execution rules, by which one work-item runs,
follow in sections of their own.
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
  /-- `alloc t c a n` allocates room for `c` values of the core type `t` in
  the memory `n`, aligned to `a` units, or to the type's default alignment
  there when `a` is `none`, for the whole run of the kernel, and gives the
  pointer to the allocation, a `ptr<n>`. -/
  | alloc (t : Core.Ty) (c : Nat) (a : Option Nat) (n : Nat)
  deriving Repr, DecidableEq

end Fir.Gpu

namespace Fir

/-- The dialect `gpu` on its own: its ops, and no types of its own. -/
abbrev GpuExt : Dialect := ⟨Gpu.Op, Empty⟩

/-- Its name, the word before the `.` of each of its words. -/
instance Gpu.instDialectName : DialectName GpuExt := ⟨"gpu"⟩

/-- The dialect `gpu` over the core: its ops, at the core's types. -/
abbrev GpuDialect : Dialect := CoreDialect.over GpuExt

/-- The sum of the core and `gpu`: what `funk`, `fir-ref fmt`,
`fir-ref validate` and `fir-ref run` read. -/
abbrev CoreGpu : Dialect := CoreDialect ⊞ GpuExt

namespace Gpu

/-- An op of `gpu` takes no operand. -/
def Op.sig : Op → List (Core.Ty ⊕ Empty)
  | .query .. | .alloc .. => []

/-- A question gives one integer, of the width of its instance, and an
allocation the core's pointer of its memory. -/
def Op.returnTypes : Op → List (Core.Ty ⊕ Empty)
  | .query _ _ w => [.inl (.int w)]
  | .alloc _ _ _ n => [.inl (.ptr n)]

/-- No op of `gpu` ends a block, has a successor or owns a region. -/
instance instDialectSignature : DialectSignature GpuDialect where
  sig := Op.sig
  returnTypes := Op.returnTypes
  isTerminator _ := false
  succCount _ := 0

end Gpu

end Fir
