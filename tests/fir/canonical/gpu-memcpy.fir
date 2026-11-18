layout memory(3, unit(16), pointer(32), little)

module @dev() {
  dialects gpu

  func @buffer() -> ptr(3) {
  ^entry:
    %p: ptr(3) = gpu.work_group_alloca i32 8 align(4) @0
    ret %p @0
  }

  func @copy(%v: i32) -> i32 {
  ^entry:
    %p: ptr(3) = call @buffer @1
    %i: i32 = gpu.work_item_id gpu.x @1
    %two: i32 = const 2 @1
    %o: i32 = mul %i, %two @1
    %q: ptr(3) = ptradd %p, %o @1
    store nonatomic %v, %q @1
    %e: i32 = const 8 @1
    %r: ptr(3) = ptradd %q, %e @1
    memcpy nonatomic %r, %q, %two @1
    %w: i32 = load nonatomic %r @1
    ret %w @1
  }

  func @move(%v: i32, %n: i32) -> i32 {
  ^entry:
    %p: ptr(3) = gpu.work_group_alloca i32 2 @2
    store nonatomic %v, %p @2
    %one: i32 = const 1 @2
    %q: ptr(3) = ptradd %p, %one @2
    memmove nonatomic %q, %p, %n @2
    %w: i32 = load nonatomic align(1) %q @2
    ret %w @2
  }

}

locs {
  @0 = unknown
  @1 = unknown
  @2 = unknown
}
