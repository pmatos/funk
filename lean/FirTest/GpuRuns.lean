import FirTest.Run

/-!
Tests of the runs of one work-item of `gpu` (ADR-2026-11-09-1545, #212's
second stage), on `FirRef.runBytes`, which computes what `fir-ref run`
reports. A run reads the sum of the core and `gpu`, names a kernel of a
device module as `@dev::@k`, and takes the work-item as its input. The
kernels' memory ops run on the memories of the host's data layout, here a
memory other than 0 with units of 16 bits and pointers of 32 bits, and one
with units of 8 bits and pointers of 16 bits: `alloca`, `load`, `store` and
`ptradd`, of integers and of pointers, as they run on the default memory
(#231). `gpu.work_group_alloca` allocates in those memories for the whole
run of the kernel: its allocation outlives the call that made it, where a
stack allocation does not, and the core's ops work on it unchanged
(the human's ruling of 2026-11-16 on #212). The last checks pin the axioms
of the theorems of the sum.
-/

namespace FirTest.GpuRuns

open Fir FirRef

/-- A host module with a device module, whose kernels ask the work-item and
use the host's memories 3 and 5. -/
def kernels : String := "layout memory(3, unit(16), pointer(32), little), memory(5, unit(8), pointer(16), little)

func @host(%a: i32) -> i32 {
^e:
  ret %a @0
}

module @dev() {
  dialects gpu

  func @global_id() -> i32 {
  ^e:
    %i: i32 = gpu.work_item_id gpu.x @0
    %g: i32 = gpu.work_group_id gpu.x @0
    %s: i32 = gpu.work_group_size gpu.x @0
    %t: i32 = mul %g, %s @0
    %r: i32 = add %t, %i @0
    ret %r @0
  }

  func @count() -> i32, i32 {
  ^e:
    %y: i32 = gpu.num_work_groups gpu.y @0
    %z: i32 = gpu.work_group_size gpu.z @0
    ret %y, %z @0
  }

  func @slot(%v: i32) -> i32 {
  ^e:
    %i: i32 = gpu.work_item_id gpu.x @0
    %two: i32 = const 2 @0
    %o: i32 = mul %i, %two @0
    %p: ptr(3) = alloca stack i32 8 @0
    %q: ptr(3) = ptradd %p, %o @0
    store nonatomic %v, %q @0
    %pp: ptr(5) = alloca stack ptr(3) @0
    store nonatomic %q, %pp @0
    %r: ptr(3) = load nonatomic %pp @0
    %w: i32 = load nonatomic %r @0
    ret %w @0
  }

  func @where() -> ptr(3) {
  ^e:
    %p: ptr(3) = alloca stack i16 @0
    %one: i32 = const 1 @0
    %q: ptr(3) = ptradd %p, %one @0
    ret %q @0
  }

  module @inner() {
    dialects gpu

    func @k() -> i32 {
    ^e:
      %i: i32 = gpu.work_item_id gpu.z @0
      ret %i @0
    }
  }
}

locs {
  @0 = unknown
}
"

/-- A work-item: its ids and sizes in `gpu.x`, the rest one work-item of
one work-group. -/
@[instance_reducible] def item (id group size count : Nat) : Gpu.WorkItem :=
  ⟨fun | .x => id | _ => 0, fun | .x => group | _ => 0, fun | .x => size | _ => 1,
    fun | .x => count | _ => 1⟩

/-- What `fir-ref run` reports on `kernels` as the work-item `w`. -/
def runKernel (func : String) (args : List String := []) (w : Gpu.WorkItem := .single) :
    RunReport :=
  runBytes "t.fir" kernels.toUTF8 defaultFuel func args (.scripted []) w

-- The text is a valid module of the sum.
#guard match (Fir.parse kernels : Except ParseError (Module CoreGpu)) with
  | .ok m => m.allProblems.isEmpty
  | .error _ => false

-- A host function runs as before, and a kernel by its path.
#guard runKernel "@host" ["7"] == returns ["7"]
#guard runKernel "@dev::@global_id" == returns ["0"]
#guard runKernel "@dev::@global_id" (w := item 3 2 4 5) == returns ["11"]
#guard runKernel "@dev::@count" (w := ⟨fun _ => 0, fun _ => 0, fun _ => 6, fun _ => 9⟩) ==
  returns ["9", "6"]
-- A module nested in a device module, at any depth.
#guard runKernel "@dev::@inner::@k" (w := ⟨fun _ => 4, fun _ => 0, fun _ => 5, fun _ => 1⟩) ==
  returns ["4"]

-- `alloca`, `load`, `store` and `ptradd` run in memories 3 and 5 of the
-- host's layout: the work-item picks its own slot, two units of 16 bits
-- each, and a pointer to it is stored in memory 5 and loaded back.
#guard runKernel "@dev::@slot" ["-5"] (w := item 3 0 8 1) == returns ["-5"]
#guard runKernel "@dev::@slot" ["123456"] (w := item 7 0 8 1) == returns ["123456"]
-- Past the end of the allocation, a store is UB.
#guard (runKernel "@dev::@slot" ["1"] (w := item 8 0 9 1)).out ==
  "{\"kind\":\"ub\",\"reason\":\"an access out of bounds\",\"choices\":0}"
-- An offset counts units of the pointer's memory.
#guard runKernel "@dev::@where" == returns ["ptr(0, 1)"]

-- A path names a function of a nested module, and nothing else.
#guard (runKernel "@dev").err == "fir-ref: t.fir has no function @dev"
#guard (runKernel "@dev::@nope").err == "fir-ref: t.fir has no function @dev::@nope"
#guard (runKernel "@global_id").err == "fir-ref: t.fir has no function @global_id"
#guard (runKernel "@dev::").status == 2

/-! # Work-group memory -/

/-- Kernels that allocate in work-group memory, memories 3 and 5 of the
host's layout, with integer and pointer elements. -/
def workGroup : String := "layout memory(3, unit(16), pointer(32), little), memory(5, unit(8), pointer(16), little)

module @dev() {
  dialects gpu

  func @buffer() -> ptr(3) {
  ^e:
    %p: ptr(3) = gpu.work_group_alloca i32 8 align(4) @0
    ret %p @0
  }

  func @frame() -> ptr(3) {
  ^e:
    %p: ptr(3) = alloca stack i32 8 align(4) @0
    ret %p @0
  }

  func @keep(%v: i32) -> i32 {
  ^e:
    %p: ptr(3) = call @buffer @0
    %i: i32 = gpu.work_item_id gpu.x @0
    %two: i32 = const 2 @0
    %o: i32 = mul %i, %two @0
    %q: ptr(3) = ptradd %p, %o @0
    store nonatomic %v, %q @0
    %pp: ptr(5) = gpu.work_group_alloca ptr(3) 2 @0
    %four: i32 = const 4 @0
    %pq: ptr(5) = ptradd %pp, %four @0
    store nonatomic %q, %pq @0
    %r: ptr(3) = load nonatomic %pq @0
    %w: i32 = load nonatomic %r @0
    ret %w @0
  }

  func @lose(%v: i32) -> i32 {
  ^e:
    %p: ptr(3) = call @frame @0
    store nonatomic %v, %p @0
    %w: i32 = load nonatomic %p @0
    ret %w @0
  }

  func @both() -> ptr(3), ptr(3) {
  ^e:
    %w: ptr(3) = gpu.work_group_alloca i32 @0
    %s: ptr(3) = alloca stack i32 @0
    ret %w, %s @0
  }

  func @kept(%v: i32) -> i32 {
  ^e:
    %w: ptr(3), %s: ptr(3) = call @both @0
    store nonatomic %v, %w @0
    %r: i32 = load nonatomic %w @0
    ret %r @0
  }

  func @dropped(%v: i32) -> i32 {
  ^e:
    %w: ptr(3), %s: ptr(3) = call @both @0
    store nonatomic %v, %s @0
    %r: i32 = load nonatomic %s @0
    ret %r @0
  }

  func @twice() -> ptr(3), ptr(3) {
  ^e:
    %p: ptr(3) = call @buffer @0
    %q: ptr(3) = call @buffer @0
    ret %p, %q @0
  }
}

locs {
  @0 = unknown
}
"

/-- What `fir-ref run` reports on `workGroup` as the work-item `w`. -/
def runWorkGroup (func : String) (args : List String := []) (w : Gpu.WorkItem := .single) :
    RunReport :=
  runBytes "t.fir" workGroup.toUTF8 defaultFuel func args (.scripted []) w

#guard match (Fir.parse workGroup : Except ParseError (Module CoreGpu)) with
  | .ok m => m.allProblems.isEmpty
  | .error _ => false

-- The allocation outlives the call that made it: the kernel stores through
-- it and loads back, an `i32` of two 16-bit units, and a pointer of memory 3
-- in the second slot of a work-group allocation of memory 5.
#guard runWorkGroup "@dev::@keep" ["-5"] (w := item 3 0 8 1) == returns ["-5"]
#guard runWorkGroup "@dev::@keep" ["123456"] (w := item 7 0 8 1) == returns ["123456"]
#guard (runWorkGroup "@dev::@keep" ["1"] (w := item 8 0 9 1)).out ==
  "{\"kind\":\"ub\",\"reason\":\"an access out of bounds\",\"choices\":0}"
-- A stack allocation does not: its call's frame frees it.
#guard (runWorkGroup "@dev::@lose" ["1"]).out ==
  "{\"kind\":\"ub\",\"reason\":\"an access to a freed allocation\",\"choices\":0}"
-- In one memory, a work-group allocation and a stack allocation made by
-- the same call: the first outlives the call, the second does not.
#guard runWorkGroup "@dev::@both" == returns ["ptr(0, 0)", "ptr(1, 0)"]
#guard runWorkGroup "@dev::@kept" ["9"] == returns ["9"]
#guard (runWorkGroup "@dev::@dropped" ["9"]).out ==
  "{\"kind\":\"ub\",\"reason\":\"an access to a freed allocation\",\"choices\":0}"
-- Each run of the op makes a new allocation.
#guard runWorkGroup "@dev::@twice" == returns ["ptr(0, 0)", "ptr(1, 0)"]

/-! # The theorems' axioms -/

/-- info: 'Fir.Gpu.lawfulDialectEffects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Gpu.lawfulDialectEffects

/-- info: 'Fir.Gpu.lawfulTotal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Gpu.lawfulTotal

/-- info: 'Fir.Gpu.lawfulMonotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Gpu.lawfulMonotone

/-- info: 'Fir.Gpu.lawfulMemPoison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Gpu.lawfulMemPoison

/-- info: 'Fir.Gpu.progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Gpu.progress

/-- info: 'Fir.Gpu.args_isRefinedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Gpu.args_isRefinedBy

/-- info: 'Fir.Gpu.replaceBody_isRefinedBy_of_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Gpu.replaceBody_isRefinedBy_of_from

/-- info: 'Fir.Gpu.exhaustive_memOutcomes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Gpu.exhaustive_memOutcomes

end FirTest.GpuRuns
