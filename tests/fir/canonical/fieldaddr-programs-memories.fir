layout memory(1, unit(16), pointer(32), little)

aggregate @point() memory(1) size(12) align(4) field(0, i16) field(2, f32) field(4, f64) field(8, ptr(1)) field(10, i8) {
}

aggregate @row() memory(1) size(8) align(2) field(0, i24, 4) {
}

aggregate @node() memory(1) size(8) align(4) field(0, i32) field(2, ptr(1)) field(4, ptr) {
}

func @point_fields(%a: i16, %b: f32, %c: f64, %d: i8) -> i16, f32, f64, i8 {
^entry:
  %p: ptr(1) = alloca stack i16 12 align(4) @0
  %fa: ptr(1) = fieldaddr @point 0 %p @0
  %fb: ptr(1) = fieldaddr @point 1 %p @0
  %fc: ptr(1) = fieldaddr @point 2 %p @0
  %fd: ptr(1) = fieldaddr @point 3 %p @0
  %fe: ptr(1) = fieldaddr @point 4 %p @0
  store nonatomic %a, %fa @0
  store nonatomic %b, %fb @0
  store nonatomic %c, %fc @0
  store nonatomic %p, %fd @0
  store nonatomic %d, %fe @0
  %eight: i64 = const 8 @0
  %s: ptr(1) = ptradd %p, %eight @0
  %self: ptr(1) = load nonatomic %s @0
  %x: i16 = load nonatomic %self @0
  %two: i64 = const 2 @0
  %b2: ptr(1) = ptradd %self, %two @0
  %y: f32 = load nonatomic %b2 @0
  %four: i64 = const 4 @0
  %b4: ptr(1) = ptradd %self, %four @0
  %z: f64 = load nonatomic %b4 @0
  %ten: i64 = const 10 @0
  %b10: ptr(1) = ptradd %self, %ten @0
  %w: i8 = load nonatomic %b10 @0
  ret %x, %y, %z, %w @0
}

func @row_sum(%n: i24) -> i24 {
^entry:
  %p: ptr(1) = alloca stack i24 4 @0
  %zero: i24 = const 0 @0
  %one: i24 = const 1 @0
  %four: i24 = const 4 @0
  %ten: i24 = const 10 @0
  br ^fill(%zero) @0
^fill(%i: i24):
  %e: ptr(1) = fieldaddr @row 0 %p, %i @0
  %t: i24 = mul %i, %ten @0
  %v: i24 = add %t, %n @0
  store nonatomic %v, %e @0
  %i1: i24 = add %i, %one @0
  %more: i1 = icmp slt %i1, %four @0
  cond_br %more, ^fill(%i1), ^sum(%zero, %zero) @0
^sum(%j: i24, %acc: i24):
  %f: ptr(1) = fieldaddr @row 0 %p, %j @0
  %w: i24 = load nonatomic %f @0
  %acc1: i24 = add %acc, %w @0
  %j1: i24 = add %j, %one @0
  %again: i1 = icmp slt %j1, %four @0
  cond_br %again, ^sum(%j1, %acc1), ^done @0
^done:
  ret %acc1 @0
}

func @row_at(%k: i32) -> i24 {
^entry:
  %p: ptr(1) = alloca stack i24 4 @0
  %v: i24 = const -7 @0
  %e: ptr(1) = fieldaddr @row 0 %p, %k @0
  store nonatomic %v, %e @0
  %two: i64 = const 2 @0
  %k64: i64 = sext %k @0
  %off: i64 = mul %k64, %two @0
  %q: ptr(1) = ptradd %p, %off @0
  %r: i24 = load nonatomic %q @0
  ret %r @0
}

func @list_sum() -> i32 {
^entry:
  %a: ptr(1) = alloca stack i32 4 align(4) @0
  %b: ptr(1) = alloca stack i32 4 align(4) @0
  %zero: i32 = const 0 @0
  %one: i32 = const 1 @0
  %two: i32 = const 2 @0
  %v1: i32 = const 40 @0
  %v2: i32 = const 2 @0
  %av: ptr(1) = fieldaddr @node 0 %a @0
  %an: ptr(1) = fieldaddr @node 1 %a @0
  %bv: ptr(1) = fieldaddr @node 0 %b @0
  store nonatomic %v1, %av @0
  store nonatomic %b, %an @0
  store nonatomic %v2, %bv @0
  br ^walk(%a, %zero, %zero) @0
^walk(%p: ptr(1), %k: i32, %acc: i32):
  %v: ptr(1) = fieldaddr @node 0 %p @0
  %x: i32 = load nonatomic %v @0
  %acc1: i32 = add %acc, %x @0
  %k1: i32 = add %k, %one @0
  %more: i1 = icmp ult %k1, %two @0
  cond_br %more, ^next, ^done @0
^next:
  %n: ptr(1) = fieldaddr @node 1 %p @0
  %q: ptr(1) = load nonatomic %n @0
  br ^walk(%q, %k1, %acc1) @0
^done:
  ret %acc1 @0
}

func @other_memory(%v: i64) -> i64 {
^entry:
  %node: ptr(1) = alloca stack i32 4 align(4) @0
  %cell: ptr = alloca stack i64 @0
  store nonatomic %v, %cell @0
  %f: ptr(1) = fieldaddr @node 2 %node @0
  store nonatomic %cell, %f @0
  %four: i64 = const 4 @0
  %q: ptr(1) = ptradd %node, %four @0
  %back: ptr = load nonatomic %q @0
  %r: i64 = load nonatomic %back @0
  ret %r @0
}

locs {
  @0 = unknown
}
