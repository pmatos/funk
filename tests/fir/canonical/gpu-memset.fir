layout memory(3, unit(16), pointer(32), little)

module @dev() {
  dialects gpu

  func @buffer() -> ptr(3) {
  ^entry:
    %p: ptr(3) = gpu.work_group_alloca i32 8 align(4) @0
    ret %p @0
  }

  func @fill(%v: i16) -> i32 {
  ^entry:
    %p: ptr(3) = call @buffer @1
    %i: i32 = gpu.work_item_id gpu.x @1
    %two: i32 = const 2 @1
    %o: i32 = mul %i, %two @1
    %e: i32 = const 8 @1
    %k: i32 = add %o, %e @1
    %q: ptr(3) = ptradd %p, %k @1
    memset nonatomic %q, %v, %two @1
    %w: i32 = load nonatomic %q @1
    ret %w @1
  }

}

locs {
  @0 = unknown
  @1 = unknown
}
