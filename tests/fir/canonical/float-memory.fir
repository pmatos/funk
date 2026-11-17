layout memory(1, unit(16), pointer(32), little)

func @round_f16(%v: f16) -> f16 {
^entry:
  %p: ptr = alloca stack f16 @0
  store nonatomic %v, %p @0
  %r: f16 = load nonatomic %p @0
  ret %r @0
}

func @round_bf16(%v: bf16) -> bf16 {
^entry:
  %p: ptr = alloca stack bf16 @0
  store nonatomic %v, %p @0
  %r: bf16 = load nonatomic %p @0
  ret %r @0
}

func @round_f32(%v: f32) -> f32 {
^entry:
  %p: ptr = alloca stack f32 @0
  store nonatomic %v, %p @0
  %r: f32 = load nonatomic %p @0
  ret %r @0
}

func @round_f64(%v: f64) -> f64 {
^entry:
  %p: ptr = alloca stack f64 @0
  store nonatomic %v, %p @0
  %r: f64 = load nonatomic %p @0
  ret %r @0
}

func @round_f128(%v: f128) -> f128 {
^entry:
  %p: ptr = alloca stack f128 @0
  store nonatomic %v, %p @0
  %r: f128 = load nonatomic %p @0
  ret %r @0
}

func @round_tiny(%v: float(2, 1)) -> float(2, 1) {
^entry:
  %p: ptr = alloca stack float(2, 1) @0
  store nonatomic %v, %p @0
  %r: float(2, 1) = load nonatomic %p @0
  ret %r @0
}

func @f16_bits(%v: f16) -> i16 {
^entry:
  %p: ptr = alloca stack f16 @0
  store nonatomic %v, %p @0
  %r: i16 = load nonatomic %p @0
  ret %r @0
}

func @bf16_of_bits(%b: i16) -> bf16 {
^entry:
  %p: ptr = alloca stack i16 @0
  store nonatomic %b, %p @0
  %r: bf16 = load nonatomic %p @0
  ret %r @0
}

func @f32_bits(%v: f32) -> i32 {
^entry:
  %p: ptr = alloca stack f32 @0
  store nonatomic %v, %p @0
  %r: i32 = load nonatomic %p @0
  ret %r @0
}

func @f32_of_bits(%b: i32) -> f32 {
^entry:
  %p: ptr = alloca stack i32 @0
  store nonatomic %b, %p @0
  %r: f32 = load nonatomic %p @0
  ret %r @0
}

func @f64_bits(%v: f64) -> i64 {
^entry:
  %p: ptr = alloca stack f64 @0
  store nonatomic %v, %p @0
  %r: i64 = load nonatomic %p @0
  ret %r @0
}

func @f64_of_bits(%b: i64) -> f64 {
^entry:
  %p: ptr = alloca stack i64 @0
  store nonatomic %b, %p @0
  %r: f64 = load nonatomic %p @0
  ret %r @0
}

func @f128_bits(%v: f128) -> i128 {
^entry:
  %p: ptr = alloca stack f128 @0
  store nonatomic %v, %p @0
  %r: i128 = load nonatomic %p @0
  ret %r @0
}

func @tiny_byte(%v: float(2, 1)) -> i8 {
^entry:
  %p: ptr = alloca stack float(2, 1) @0
  store nonatomic %v, %p @0
  %r: i8 = load nonatomic %p @0
  ret %r @0
}

func @tiny_of_byte(%b: i8) -> float(2, 1) {
^entry:
  %p: ptr = alloca stack i8 @0
  store nonatomic %b, %p @0
  %r: float(2, 1) = load nonatomic %p @0
  ret %r @0
}

func @f32_top_byte(%v: f32) -> i8 {
^entry:
  %p: ptr = alloca stack f32 @0
  store nonatomic %v, %p @0
  %three: i64 = const 3 @0
  %q: ptr = ptradd %p, %three @0
  %r: i8 = load nonatomic %q @0
  ret %r @0
}

func @nan_constant() -> f32 {
^entry:
  %n: f32 = const 0xffc00123 @0
  %p: ptr = alloca stack f32 @0
  store nonatomic %n, %p @0
  %r: f32 = load nonatomic %p @0
  ret %r @0
}

func @nan_result(%a: f64, %b: f64) -> f64 {
^entry:
  %n: f64 = fsub round(rne) %a, %b @0
  %p: ptr = alloca stack f64 @0
  store nonatomic %n, %p @0
  %r: f64 = load nonatomic %p @0
  ret %r @0
}

func @at_index(%v: f32, %k: i64) -> f32 {
^entry:
  %p: ptr = alloca stack f32 3 @0
  %q: ptr = ptradd %p, %k @0
  store nonatomic %v, %q @0
  %r: f32 = load nonatomic %q @0
  ret %r @0
}

func @at_offset(%v: f64, %k: i64) -> f64 {
^entry:
  %p: ptr = alloca stack f64 2 @0
  %q: ptr = ptradd %p, %k @0
  store nonatomic %v, %q @0
  %r: f64 = load nonatomic %q @0
  ret %r @0
}

func @at_offset_four(%v: f64, %k: i64) -> f64 {
^entry:
  %p: ptr = alloca stack f64 2 @0
  %q: ptr = ptradd %p, %k @0
  store nonatomic align(4) %v, %q @0
  %r: f64 = load nonatomic align(4) %q @0
  ret %r @0
}

func @in_bytes(%v: f32) -> f32 {
^entry:
  %p: ptr = alloca stack i8 4 @0
  store nonatomic %v, %p @0
  %r: f32 = load nonatomic %p @0
  ret %r @0
}

func @fresh() -> f64 {
^entry:
  %p: ptr = alloca stack f64 @0
  %r: f64 = load nonatomic %p @0
  ret %r @0
}

func @pointer_units() -> f64 {
^entry:
  %x: ptr = alloca stack i8 @0
  %p: ptr = alloca stack ptr @0
  store nonatomic %x, %p @0
  %r: f64 = load nonatomic %p @0
  ret %r @0
}

func @stored_poison(%v: f32) -> f32 {
^entry:
  %p: ptr = alloca stack f32 @0
  store nonatomic %v, %p @0
  %r: f32 = load nonatomic %p @0
  ret %r @0
}

func @load_through(%p: ptr) -> f32 {
^entry:
  %r: f32 = load nonatomic %p @0
  ret %r @0
}

func @store_through(%p: ptr, %v: f16) -> f16 {
^entry:
  store nonatomic %v, %p @0
  ret %v @0
}

func @in_units(%v: f32) -> i16 {
^entry:
  %p: ptr(1) = alloca stack f32 @0
  store nonatomic %v, %p @0
  %one: i64 = const 1 @0
  %q: ptr(1) = ptradd %p, %one @0
  %r: i16 = load nonatomic %q @0
  ret %r @0
}

func @round_in_units(%v: f64) -> f64 {
^entry:
  %p: ptr(1) = alloca stack f64 @0
  store nonatomic %v, %p @0
  %r: f64 = load nonatomic %p @0
  ret %r @0
}

func @misaligned_in_units(%v: f64) -> f64 {
^entry:
  %p: ptr(1) = alloca stack f64 2 @0
  %two: i64 = const 2 @0
  %q: ptr(1) = ptradd %p, %two @0
  store nonatomic %v, %q @0
  %r: f64 = load nonatomic %q @0
  ret %r @0
}

locs {
  @0 = unknown
}
