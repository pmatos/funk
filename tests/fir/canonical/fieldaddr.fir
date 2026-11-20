layout memory(1, unit(16), pointer(32), little)

aggregate @pair() memory(0) size(16) align(8) field(0, i64) field(8, i64) {
}

aggregate @i24s() memory(0) size(16) align(4) field(0, i24, 4) {
}

aggregate @wide() memory(1) size(6) align(2) field(0, ptr(1)) field(2, i16, 4) {
}

aggregate @long_doubles() memory(0) size(32) align(16) field(0, float(15, 64), 2) {
}

func @pair_fields(%a: i64, %b: i64) -> i64, i64 {
^entry:
  %p: ptr = alloca stack i64 2 @0
  %f0: ptr = fieldaddr @pair 0 %p @0
  %f1: ptr = fieldaddr @pair 1 %p @0
  store nonatomic %a, %f0 @0
  store nonatomic %b, %f1 @0
  %eight: i64 = const 8 @0
  %q: ptr = ptradd %p, %eight @0
  %x: i64 = load nonatomic %p @0
  %y: i64 = load nonatomic %q @0
  ret %x, %y @0
}

func @elements() -> i24, i24, i24, i24 {
^entry:
  %p: ptr = alloca stack i32 4 @0
  %k1: i1 = const false @0
  %e1: ptr = fieldaddr @i24s 0 %p, %k1 @0
  %v1: i24 = const 10 @0
  store nonatomic %v1, %e1 @0
  %k7: i7 = const 1 @0
  %e7: ptr = fieldaddr @i24s 0 %p, %k7 @0
  %v7: i24 = const 11 @0
  store nonatomic %v7, %e7 @0
  %k8: i8 = const 2 @0
  %e8: ptr = fieldaddr @i24s 0 %p, %k8 @0
  %v8: i24 = const 12 @0
  store nonatomic %v8, %e8 @0
  %k16: i16 = const 3 @0
  %e16: ptr = fieldaddr @i24s 0 %p, %k16 @0
  %v16: i24 = const 13 @0
  store nonatomic %v16, %e16 @0
  %k32: i32 = const 3 @0
  %e32: ptr = fieldaddr @i24s 0 %p, %k32 @0
  %v32: i24 = const 14 @0
  store nonatomic %v32, %e32 @0
  %k33: i33 = const 2 @0
  %e33: ptr = fieldaddr @i24s 0 %p, %k33 @0
  %v33: i24 = const 15 @0
  store nonatomic %v33, %e33 @0
  %k64: i64 = const 1 @0
  %e64: ptr = fieldaddr @i24s 0 %p, %k64 @0
  %v64: i24 = const 16 @0
  store nonatomic %v64, %e64 @0
  %k128: i128 = const 0 @0
  %e128: ptr = fieldaddr @i24s 0 %p, %k128 @0
  %v128: i24 = const 17 @0
  store nonatomic %v128, %e128 @0
  %four: i64 = const 4 @0
  %q1: ptr = ptradd %p, %four @0
  %q2: ptr = ptradd %q1, %four @0
  %q3: ptr = ptradd %q2, %four @0
  %x0: i24 = load nonatomic %p @0
  %x1: i24 = load nonatomic %q1 @0
  %x2: i24 = load nonatomic %q2 @0
  %x3: i24 = load nonatomic %q3 @0
  ret %x0, %x1, %x2, %x3 @0
}

func @element(%v: i24, %k: i8) -> i8 {
^entry:
  %p: ptr = alloca stack i32 4 @0
  %e: ptr = fieldaddr @i24s 0 %p, %k @0
  store nonatomic %v, %e @0
  %four: i64 = const 4 @0
  %b: ptr = ptradd %p, %four @0
  %x: i8 = load nonatomic %b @0
  ret %x @0
}

func @wide_element(%v: i16, %k: i32) -> i16 {
^entry:
  %p: ptr(1) = alloca stack i16 6 @0
  %e: ptr(1) = fieldaddr @wide 1 %p, %k @0
  store nonatomic %v, %e @0
  %four: i64 = const 4 @0
  %b: ptr(1) = ptradd %p, %four @0
  %x: i16 = load nonatomic %b @0
  ret %x @0
}

func @long_double_stride(%v: f64) -> f64 {
^entry:
  %p: ptr = alloca stack i8 32 align(16) @0
  %one: i8 = const 1 @0
  %e: ptr = fieldaddr @long_doubles 0 %p, %one @0
  %x: float(15, 64) = fpext %v @0
  store nonatomic %x, %e @0
  %sixteen: i64 = const 16 @0
  %q: ptr = ptradd %p, %sixteen @0
  %y: float(15, 64) = load nonatomic %q @0
  %r: f64 = fptrunc round(rne) %y @0
  ret %r @0
}

locs {
  @0 = unknown
}
