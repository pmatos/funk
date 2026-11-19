aggregate @point() memory(0) size(24) align(8) field(0, i32) field(4, f32) field(8, f64) field(16, ptr) {
}

aggregate @row() memory(0) size(32) align(8) field(0, i64, 4) {
}

aggregate @node() memory(0) size(16) align(8) field(0, i64) field(8, ptr) {
}

aggregate @vec() memory(0) size(20) align(4) field(0, i32) field(4, i32, 4) {
}

aggregate @tail() memory(0) size(4) align(4) field(0, i32) field(4, i16, 0) {
}

aggregate @long_doubles() memory(0) size(32) align(16) field(0, float(15, 64), 2) {
}

func @point_fields(%a: i32, %b: f32, %c: f64) -> i32, f32, f64 {
^entry:
  %p: ptr = alloca stack i8 24 align(8) @0
  %fa: ptr = fieldaddr @point 0 %p @0
  %fb: ptr = fieldaddr @point 1 %p @0
  %fc: ptr = fieldaddr @point 2 %p @0
  %fd: ptr = fieldaddr @point 3 %p @0
  store nonatomic %a, %fa @0
  store nonatomic %b, %fb @0
  store nonatomic %c, %fc @0
  store nonatomic %p, %fd @0
  %sixteen: i64 = const 16 @0
  %d: ptr = ptradd %p, %sixteen @0
  %self: ptr = load nonatomic %d @0
  %x: i32 = load nonatomic %self @0
  %four: i64 = const 4 @0
  %b4: ptr = ptradd %self, %four @0
  %y: f32 = load nonatomic %b4 @0
  %eight: i64 = const 8 @0
  %b8: ptr = ptradd %self, %eight @0
  %z: f64 = load nonatomic %b8 @0
  ret %x, %y, %z @0
}

func @row_sum(%n: i64) -> i64 {
^entry:
  %p: ptr = alloca stack i64 4 @0
  %zero: i64 = const 0 @0
  %one: i64 = const 1 @0
  %four: i64 = const 4 @0
  %ten: i64 = const 10 @0
  br ^fill(%zero) @0
^fill(%i: i64):
  %e: ptr = fieldaddr @row 0 %p, %i @0
  %t: i64 = mul %i, %ten @0
  %v: i64 = add %t, %n @0
  store nonatomic %v, %e @0
  %i1: i64 = add %i, %one @0
  %more: i1 = icmp slt %i1, %four @0
  cond_br %more, ^fill(%i1), ^sum(%zero, %zero) @0
^sum(%j: i64, %acc: i64):
  %f: ptr = fieldaddr @row 0 %p, %j @0
  %w: i64 = load nonatomic %f @0
  %acc1: i64 = add %acc, %w @0
  %j1: i64 = add %j, %one @0
  %again: i1 = icmp slt %j1, %four @0
  cond_br %again, ^sum(%j1, %acc1), ^done @0
^done:
  ret %acc1 @0
}

func @row_at(%k: i8) -> i64 {
^entry:
  %p: ptr = alloca stack i64 4 @0
  %i0: i64 = const 0 @0
  %i1: i64 = const 1 @0
  %i2: i64 = const 2 @0
  %i3: i64 = const 3 @0
  %e0: ptr = fieldaddr @row 0 %p, %i0 @0
  %e1: ptr = fieldaddr @row 0 %p, %i1 @0
  %e2: ptr = fieldaddr @row 0 %p, %i2 @0
  %e3: ptr = fieldaddr @row 0 %p, %i3 @0
  %v0: i64 = const 100 @0
  %v1: i64 = const 101 @0
  %v2: i64 = const 102 @0
  %v3: i64 = const 103 @0
  store nonatomic %v0, %e0 @0
  store nonatomic %v1, %e1 @0
  store nonatomic %v2, %e2 @0
  store nonatomic %v3, %e3 @0
  %e: ptr = fieldaddr @row 0 %p, %k @0
  %r: i64 = load nonatomic %e @0
  ret %r @0
}

func @one_past(%v: i64) -> i64 {
^entry:
  %p: ptr = alloca stack i64 4 @0
  %three: i64 = const 3 @0
  %last: ptr = fieldaddr @row 0 %p, %three @0
  store nonatomic %v, %last @0
  %four: i64 = const 4 @0
  %end: ptr = fieldaddr @row 0 %p, %four @0
  %back: i64 = const -8 @0
  %q: ptr = ptradd %end, %back @0
  %r: i64 = load nonatomic %q @0
  ret %r @0
}

func @list_sum() -> i64 {
^entry:
  %a: ptr = alloca stack i64 2 @0
  %b: ptr = alloca stack i64 2 @0
  %c: ptr = alloca stack i64 2 @0
  %zero: i64 = const 0 @0
  %one: i64 = const 1 @0
  %two: i64 = const 2 @0
  %three: i64 = const 3 @0
  %av: ptr = fieldaddr @node 0 %a @0
  %an: ptr = fieldaddr @node 1 %a @0
  %bv: ptr = fieldaddr @node 0 %b @0
  %bn: ptr = fieldaddr @node 1 %b @0
  %cv: ptr = fieldaddr @node 0 %c @0
  store nonatomic %one, %av @0
  store nonatomic %b, %an @0
  store nonatomic %two, %bv @0
  store nonatomic %c, %bn @0
  store nonatomic %three, %cv @0
  br ^walk(%a, %zero, %zero) @0
^walk(%p: ptr, %k: i64, %acc: i64):
  %v: ptr = fieldaddr @node 0 %p @0
  %x: i64 = load nonatomic %v @0
  %acc1: i64 = add %acc, %x @0
  %k1: i64 = add %k, %one @0
  %more: i1 = icmp ult %k1, %three @0
  cond_br %more, ^next, ^done @0
^next:
  %n: ptr = fieldaddr @node 1 %p @0
  %q: ptr = load nonatomic %n @0
  br ^walk(%q, %k1, %acc1) @0
^done:
  ret %acc1 @0
}

func @vec_push(%x: i32, %y: i32) -> i32, i32, i32 {
^entry:
  %p: ptr = alloca stack i32 5 @0
  %len: ptr = fieldaddr @vec 0 %p @0
  %zero: i32 = const 0 @0
  %one: i32 = const 1 @0
  store nonatomic %zero, %len @0
  %n0: i32 = load nonatomic %len @0
  %e0: ptr = fieldaddr @vec 1 %p, %n0 @0
  store nonatomic %x, %e0 @0
  %n1: i32 = add %n0, %one @0
  store nonatomic %n1, %len @0
  %m0: i32 = load nonatomic %len @0
  %e1: ptr = fieldaddr @vec 1 %p, %m0 @0
  store nonatomic %y, %e1 @0
  %m1: i32 = add %m0, %one @0
  store nonatomic %m1, %len @0
  %r: i32 = load nonatomic %len @0
  %four: i64 = const 4 @0
  %q0: ptr = ptradd %p, %four @0
  %u: i32 = load nonatomic %q0 @0
  %eight: i64 = const 8 @0
  %q1: ptr = ptradd %p, %eight @0
  %w: i32 = load nonatomic %q1 @0
  ret %r, %u, %w @0
}

func @flex_tail(%k: i64) -> i16 {
^entry:
  %p: ptr = alloca stack i32 3 @0
  %e: ptr = fieldaddr @tail 1 %p, %k @0
  %v: i16 = const 9 @0
  store nonatomic %v, %e @0
  %r: i16 = load nonatomic %e @0
  ret %r @0
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
