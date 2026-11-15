layout memory(3, unit(16), pointer(32), little), memory(5, unit(8), pointer(16), little)

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
