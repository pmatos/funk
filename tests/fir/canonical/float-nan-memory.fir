func @f32_bits(%a: f32, %b: f32) -> i32 {
^entry:
  %n: f32 = fsub round(rne) %a, %b @0
  %i: i32 = bitcast %n @0
  %p: ptr = alloca stack i32 @0
  store nonatomic %i, %p @0
  %r: i32 = load nonatomic %p @0
  ret %r @0
}

func @f32_top(%a: f32, %b: f32) -> i8 {
^entry:
  %n: f32 = fsub round(rne) %a, %b @0
  %i: i32 = bitcast %n @0
  %p: ptr = alloca stack i32 @0
  store nonatomic %i, %p @0
  %three: i64 = const 3 @0
  %q: ptr = ptradd %p, %three @0
  %r: i8 = load nonatomic %q @0
  ret %r @0
}

func @f64_bits(%a: f64, %b: f64) -> i64 {
^entry:
  %n: f64 = fsub round(rne) %a, %b @0
  %i: i64 = bitcast %n @0
  %p: ptr = alloca stack i64 @0
  store nonatomic %i, %p @0
  %r: i64 = load nonatomic %p @0
  ret %r @0
}

func @f64_top(%a: f64, %b: f64) -> i8 {
^entry:
  %n: f64 = fsub round(rne) %a, %b @0
  %i: i64 = bitcast %n @0
  %p: ptr = alloca stack i64 @0
  store nonatomic %i, %p @0
  %seven: i64 = const 7 @0
  %q: ptr = ptradd %p, %seven @0
  %r: i8 = load nonatomic %q @0
  ret %r @0
}

locs {
  @0 = unknown
}
