layout memory(1, unit(8), pointer(64), little)

global @nums() size(16) align(4) const units(1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0) {
}

global @picks() size(24) align(8) const export addr(@nums, 12) addr(@nums, 4) addr(@nums) {
}

global @n3() size(16) align(8) units(30) {
}

global @n2() size(16) align(8) units(20) zeros(7) addr(@n3) {
}

global @n1() size(16) align(8) units(10) zeros(7) addr(@n2) {
}

global @count() size(8) align(8) {
}

global @buf() size(16) align(16) export {
}

global @self() size(16) align(8) addr(@self, 8) units(5) {
}

global @wide() memory(1) size(8) align(256) units(7) {
}

global @to_wide() size(8) align(8) const addr(@wide) {
}

func @pick(%i: i64) -> i32 {
^entry:
  %t: ptr = globaladdr @picks @0
  %k: i64 = const 8 @0
  %o: i64 = mul %i, %k @0
  %e: ptr = ptradd %t, %o @0
  %p: ptr = load nonatomic %e @0
  %v: i32 = load nonatomic %p @0
  ret %v @0
}

func @nth(%k: i32) -> i64 {
^entry:
  %first: ptr = globaladdr @n1 @1
  br ^loop(%first, %k) @1
^loop(%q: ptr, %i: i32):
  %zero: i32 = const 0 @1
  %more: i1 = icmp sgt %i, %zero @1
  cond_br %more, ^next, ^done @1
^next:
  %eight: i64 = const 8 @1
  %np: ptr = ptradd %q, %eight @1
  %n: ptr = load nonatomic %np @1
  %one: i32 = const 1 @1
  %i1: i32 = sub %i, %one @1
  br ^loop(%n, %i1) @1
^done:
  %v: i64 = load nonatomic %q @1
  ret %v @1
}

func @tick() -> i64 {
^entry:
  %c: ptr = globaladdr @count @2
  %v: i64 = load nonatomic %c @2
  %one: i64 = const 1 @2
  %w: i64 = add %v, %one @2
  store nonatomic %w, %c @2
  ret %w @2
}

func @ticks(%n: i32) -> i64 {
^entry:
  %zero: i32 = const 0 @2
  br ^loop(%zero) @2
^loop(%i: i32):
  %more: i1 = icmp slt %i, %n @2
  cond_br %more, ^body, ^done @2
^body:
  %t: i64 = call @tick @2
  %one: i32 = const 1 @2
  %i1: i32 = add %i, %one @2
  br ^loop(%i1) @2
^done:
  %c: ptr = globaladdr @count @2
  %v: i64 = load nonatomic %c @2
  ret %v @2
}

func @copy_nums(%i: i64) -> i32 {
^entry:
  %d: ptr = globaladdr @buf @3
  %s: ptr = globaladdr @nums @3
  %n: i64 = const 16 @3
  memcpy nonatomic %d, %s, %n @3
  %k: i64 = const 4 @3
  %o: i64 = mul %i, %k @3
  %p: ptr = ptradd %d, %o @3
  %v: i32 = load nonatomic %p @3
  ret %v @3
}

func @self_offset() -> i64, i8 {
^entry:
  %s: ptr = globaladdr @self @4
  %p: ptr = load nonatomic %s @4
  %a: i64 = ptr_expose %s @4
  %b: i64 = ptr_expose %p @4
  %d: i64 = sub %b, %a @4
  %v: i8 = load nonatomic %p @4
  ret %d, %v @4
}

func @wide_aligned() -> i64, i8 {
^entry:
  %g: ptr(1) = globaladdr @wide @5
  %a: i64 = ptr_expose %g @5
  %k: i64 = const 256 @5
  %r: i64 = urem %a, %k @5
  %t: ptr = globaladdr @to_wide @5
  %p: ptr(1) = load nonatomic %t @5
  %v: i8 = load nonatomic %p @5
  ret %r, %v @5
}

locs {
  @0 = unknown
  @1 = unknown
  @2 = unknown
  @3 = unknown
  @4 = unknown
  @5 = unknown
}
