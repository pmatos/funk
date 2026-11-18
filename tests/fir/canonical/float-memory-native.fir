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

func @f32_top_byte(%v: f32) -> i8 {
^entry:
  %p: ptr = alloca stack f32 @0
  store nonatomic %v, %p @0
  %three: i64 = const 3 @0
  %q: ptr = ptradd %p, %three @0
  %r: i8 = load nonatomic %q @0
  ret %r @0
}

func @f32_array(%a: f32, %b: f32, %c: f32) -> f32, f32, f32 {
^entry:
  %p0: ptr = alloca stack f32 3 @0
  %four: i64 = const 4 @0
  %p1: ptr = ptradd %p0, %four @0
  %p2: ptr = ptradd %p1, %four @0
  store nonatomic %c, %p2 @0
  store nonatomic %b, %p1 @0
  store nonatomic %a, %p0 @0
  %x: f32 = load nonatomic %p0 @0
  %y: f32 = load nonatomic %p1 @0
  %z: f32 = load nonatomic %p2 @0
  ret %x, %y, %z @0
}

func @f64_array(%a: f64, %b: f64) -> f64, f64 {
^entry:
  %p0: ptr = alloca stack f64 2 @0
  %eight: i64 = const 8 @0
  %p1: ptr = ptradd %p0, %eight @0
  store nonatomic %b, %p1 @0
  store nonatomic %a, %p0 @0
  %x: f64 = load nonatomic %p0 @0
  %y: f64 = load nonatomic %p1 @0
  ret %x, %y @0
}

func @f64_at_four(%v: f64) -> f64 {
^entry:
  %p: ptr = alloca stack i32 3 @0
  %four: i64 = const 4 @0
  %q: ptr = ptradd %p, %four @0
  store nonatomic align(4) %v, %q @0
  %r: f64 = load nonatomic align(4) %q @0
  ret %r @0
}

func @f32_nan(%a: f32, %b: f32) -> f32 {
^entry:
  %n: f32 = fsub round(rne) %a, %b @0
  %p: ptr = alloca stack f32 @0
  store nonatomic %n, %p @0
  %r: f32 = load nonatomic %p @0
  ret %r @0
}

func @f64_nan(%a: f64, %b: f64) -> f64 {
^entry:
  %n: f64 = fsub round(rne) %a, %b @0
  %p: ptr = alloca stack f64 @0
  store nonatomic %n, %p @0
  %r: f64 = load nonatomic %p @0
  ret %r @0
}

func @f32_nan_bits(%a: f32, %b: f32) -> i32 {
^entry:
  %n: f32 = fsub round(rne) %a, %b @0
  %p: ptr = alloca stack f32 @0
  store nonatomic %n, %p @0
  %r: i32 = load nonatomic %p @0
  ret %r @0
}

func @f64_nan_bits(%a: f64, %b: f64) -> i64 {
^entry:
  %n: f64 = fsub round(rne) %a, %b @0
  %p: ptr = alloca stack f64 @0
  store nonatomic %n, %p @0
  %r: i64 = load nonatomic %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
