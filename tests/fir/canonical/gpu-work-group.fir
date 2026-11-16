layout memory(3, unit(16), pointer(32), little), memory(5, unit(8), pointer(16), little)

module @dev() {
  dialects gpu

  func @buffer() -> ptr(3) {
  ^entry:
    %p: ptr(3) = gpu.work_group_alloca i32 8 align(4) @0
    ret %p @0
  }

  func @frame() -> ptr(3) {
  ^entry:
    %p: ptr(3) = alloca stack i32 8 align(4) @0
    ret %p @0
  }

  func @shared(%v: i32) -> i32 {
  ^entry:
    %p: ptr(3) = call @buffer @1
    %i: i32 = gpu.work_item_id gpu.x @1
    %two: i32 = const 2 @1
    %o: i32 = mul %i, %two @1
    %q: ptr(3) = ptradd %p, %o @1
    store nonatomic %v, %q @1
    %pp: ptr(5) = gpu.work_group_alloca ptr(3) 2 @1
    %four: i32 = const 4 @1
    %pq: ptr(5) = ptradd %pp, %four @1
    store nonatomic %q, %pq @1
    %r: ptr(3) = load nonatomic %pq @1
    %w: i32 = load nonatomic %r @1
    ret %w @1
  }

  func @freed(%v: i32) -> i32 {
  ^entry:
    %p: ptr(3) = call @frame @2
    store nonatomic %v, %p @2
    %w: i32 = load nonatomic %p @2
    ret %w @2
  }

  func @twice() -> ptr(3), ptr(3) {
  ^entry:
    %p: ptr(3) = call @buffer @3
    %q: ptr(3) = call @buffer @3
    ret %p, %q @3
  }

  func @both() -> ptr(3), ptr(3) {
  ^entry:
    %w: ptr(3) = gpu.work_group_alloca i32 @3
    %s: ptr(3) = alloca stack i32 @3
    ret %w, %s @3
  }

  func @kept(%v: i32) -> i32 {
  ^entry:
    %w: ptr(3), %s: ptr(3) = call @both @3
    store nonatomic %v, %w @3
    %r: i32 = load nonatomic %w @3
    ret %r @3
  }

  func @dropped(%v: i32) -> i32 {
  ^entry:
    %w: ptr(3), %s: ptr(3) = call @both @3
    store nonatomic %v, %s @3
    %r: i32 = load nonatomic %s @3
    ret %r @3
  }

  func @elements() -> i32 {
  ^entry:
    %a: ptr(3) = gpu.work_group_alloca i1 @3
    %b: ptr(3) = gpu.work_group_alloca i7 @3
    %c: ptr(3) = gpu.work_group_alloca i8 @3
    %d: ptr(3) = gpu.work_group_alloca i16 @3
    %e: ptr(3) = gpu.work_group_alloca i32 @3
    %f: ptr(3) = gpu.work_group_alloca i33 @3
    %g: ptr(5) = gpu.work_group_alloca i64 @3
    %h: ptr(5) = gpu.work_group_alloca i128 @3
    %i: ptr(5) = gpu.work_group_alloca ptr(3) @3
    %v: i33 = const -1 @3
    store nonatomic %v, %f @3
    %w: i33 = load nonatomic %f @3
    %r: i32 = trunc %w @3
    ret %r @3
  }

  func @misaligned() -> ptr(3) {
  ^entry:
    %pp: ptr(5) = gpu.work_group_alloca ptr(3) align(2) @3
    %p: ptr(3) = call @buffer @3
    store nonatomic %p, %pp @3
    ret %p @3
  }

}

locs {
  @0 = "gpu-work-group.cl":1:1 to 1:20
  @1 = "gpu-work-group.cl":4:3 to 4:30
  @2 = "gpu-work-group.cl":12:3 to 12:30
  @3 = "gpu-work-group.cl":20:3 to 20:30
}
