layout memory(3, unit(16), pointer(32), little), memory(5, unit(8), pointer(16), little)

module @dev() {
  dialects gpu

  func @tile() -> ptr(3) {
  ^entry:
    %p: ptr(3) = gpu.work_group_alloca f32 8 @0
    ret %p @0
  }

  func @shared(%v: f32) -> f32 {
  ^entry:
    %p: ptr(3) = call @tile @1
    %i: i32 = gpu.work_item_id gpu.x @1
    %two: i32 = const 2 @1
    %o: i32 = mul %i, %two @1
    %q: ptr(3) = ptradd %p, %o @1
    store nonatomic %v, %q @1
    %r: f32 = load nonatomic %q @1
    ret %r @1
  }

  func @slot() -> ptr(5) {
  ^entry:
    %p: ptr(5) = gpu.work_group_alloca f64 @0
    ret %p @0
  }

  func @kept(%v: f64) -> f64 {
  ^entry:
    %p: ptr(5) = call @slot @1
    store nonatomic %v, %p @1
    %r: f64 = load nonatomic %p @1
    ret %r @1
  }

  func @round_f16(%v: f16) -> f16 {
  ^entry:
    %p: ptr(3) = gpu.work_group_alloca f16 @2
    store nonatomic %v, %p @2
    %r: f16 = load nonatomic %p @2
    ret %r @2
  }

  func @round_bf16(%v: bf16) -> bf16 {
  ^entry:
    %p: ptr(5) = gpu.work_group_alloca bf16 @2
    store nonatomic %v, %p @2
    %r: bf16 = load nonatomic %p @2
    ret %r @2
  }

  func @round_f128(%v: f128) -> f128 {
  ^entry:
    %p: ptr(3) = gpu.work_group_alloca f128 2 align(8) @2
    store nonatomic %v, %p @2
    %r: f128 = load nonatomic %p @2
    ret %r @2
  }

  func @round_tiny(%v: float(2, 1)) -> float(2, 1) {
  ^entry:
    %p: ptr(5) = gpu.work_group_alloca float(2, 1) @2
    store nonatomic %v, %p @2
    %r: float(2, 1) = load nonatomic %p @2
    ret %r @2
  }

  func @f32_bits(%v: f32) -> i32 {
  ^entry:
    %p: ptr(3) = gpu.work_group_alloca f32 @2
    store nonatomic %v, %p @2
    %r: i32 = load nonatomic %p @2
    ret %r @2
  }

  func @top_unit(%v: f32) -> i16 {
  ^entry:
    %p: ptr(3) = gpu.work_group_alloca f32 @2
    store nonatomic %v, %p @2
    %one: i32 = const 1 @2
    %q: ptr(3) = ptradd %p, %one @2
    %r: i16 = load nonatomic %q @2
    ret %r @2
  }

  func @misaligned(%v: f64) -> f64 {
  ^entry:
    %p: ptr(5) = gpu.work_group_alloca f64 2 @2
    %four: i16 = const 4 @2
    %q: ptr(5) = ptradd %p, %four @2
    store nonatomic %v, %q @2
    %r: f64 = load nonatomic %q @2
    ret %r @2
  }

  func @fresh() -> f64 {
  ^entry:
    %p: ptr(5) = gpu.work_group_alloca f64 @2
    %r: f64 = load nonatomic %p @2
    ret %r @2
  }

}

locs {
  @0 = "gpu-work-group-floats.cl":1:1 to 1:24
  @1 = "gpu-work-group-floats.cl":4:3 to 4:30
  @2 = "gpu-work-group-floats.cl":12:3 to 12:30
}
