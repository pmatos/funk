layout memory(3, unit(8), pointer(32), little)

func @host(%a: i32) -> i32 {
^entry:
  %b: i32 = add %a, %a @0
  ret %b @0
}

module @dev() {
  dialects gpu

  func @global_id() -> i32 {
  ^entry:
    %i: i32 = gpu.work_item_id gpu.x @1
    %g: i32 = gpu.work_group_id gpu.x @1
    %s: i32 = gpu.work_group_size gpu.x @1
    %t: i32 = mul %g, %s @1
    %r: i32 = add %t, %i @1
    ret %r @1
  }

  func @groups() -> i32 {
  ^entry:
    %y: i32 = gpu.num_work_groups gpu.y @2
    %z: i32 = gpu.num_work_groups gpu.z @2
    %n: i32 = mul %y, %z @2
    ret %n @2
  }

  func @scratch(%v: i32) -> i32 {
  ^entry:
    %i: i32 = gpu.work_item_id gpu.y @3
    %p: ptr(3) = alloca stack i32 64 @3
    %q: ptr(3) = ptradd %p, %i @3
    store nonatomic %v, %q @3
    %w: i32 = load nonatomic %q @3
    %pp: ptr(3) = alloca stack ptr(3) @3
    store nonatomic %q, %pp @3
    %r: ptr(3) = load nonatomic %pp @3
    %u: i32 = load nonatomic %r @3
    %s: i32 = add %w, %u @3
    ret %s @3
  }

}

locs {
  @0 = "gpu-kernel.cl":1:1 to 1:9
  @1 = "gpu-kernel.cl":4:3 to 4:30
  @2 = "gpu-kernel.cl":12:3 to 12:30
  @3 = "gpu-kernel.cl":20:3 to 20:30
}
