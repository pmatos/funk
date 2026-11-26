global @msg() size(2) align(1) const units(104, 105) {
}

global @tbl() size(16) align(8) {
}

func @inc(%x: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %r: i32 = add %x, %one @0
  ret %r @0
}

func @dec(%x: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %r: i32 = sub %x, %one @0
  ret %r @0
}

func @addresses() -> ptr, ptr {
^entry:
  %a: ptr = funcaddr @inc @0
  %b: ptr = funcaddr @dec @0
  ret %a, %b @0
}

func @load_through() -> i8 {
^entry:
  %a: ptr = funcaddr @inc @0
  %v: i8 = load nonatomic %a @0
  ret %v @0
}

func @store_through(%v: i8) {
^entry:
  %a: ptr = funcaddr @inc @0
  store nonatomic %v, %a @0
  ret @0
}

func @moved(%i: i64) -> i8 {
^entry:
  %a: ptr = funcaddr @dec @0
  %p: ptr = ptradd %a, %i @0
  %v: i8 = load nonatomic %p @0
  ret %v @0
}

func @distance() -> i64 {
^entry:
  %a: ptr = funcaddr @inc @0
  %b: ptr = funcaddr @dec @0
  %x: i64 = ptr_expose %a @0
  %y: i64 = ptr_expose %b @0
  %d: i64 = sub %y, %x @0
  ret %d @0
}

func @round_trip() -> ptr {
^entry:
  %a: ptr = funcaddr @dec @0
  %x: i64 = ptr_expose %a @0
  %p: ptr = ptr_from_int %x @0
  ret %p @0
}

func @stack_table(%i: i64) -> ptr {
^entry:
  %t: ptr = alloca stack ptr 2 @0
  %a: ptr = funcaddr @inc @0
  %b: ptr = funcaddr @dec @0
  store nonatomic %a, %t @0
  %k: i64 = const 8 @0
  %t1: ptr = ptradd %t, %k @0
  store nonatomic %b, %t1 @0
  %o: i64 = mul %i, %k @0
  %e: ptr = ptradd %t, %o @0
  %p: ptr = load nonatomic %e @0
  ret %p @0
}

func @global_table(%i: i64) -> ptr {
^entry:
  %t: ptr = globaladdr @tbl @0
  %a: ptr = funcaddr @inc @0
  %b: ptr = funcaddr @dec @0
  store nonatomic %a, %t @0
  %k: i64 = const 8 @0
  %t1: ptr = ptradd %t, %k @0
  store nonatomic %b, %t1 @0
  %o: i64 = mul %i, %k @0
  %e: ptr = ptradd %t, %o @0
  %p: ptr = load nonatomic %e @0
  ret %p @0
}

func @same(%i: i64) -> i1 {
^entry:
  %t: ptr = alloca stack ptr 2 @0
  %a: ptr = funcaddr @inc @0
  %b: ptr = funcaddr @dec @0
  store nonatomic %a, %t @0
  %k: i64 = const 8 @0
  %t1: ptr = ptradd %t, %k @0
  store nonatomic %b, %t1 @0
  %o: i64 = mul %i, %k @0
  %e: ptr = ptradd %t, %o @0
  %p: ptr = load nonatomic %e @0
  %x: i64 = ptr_expose %p @0
  %y: i64 = ptr_expose %b @0
  %c: i1 = icmp eq %x, %y @0
  ret %c @0
}

func @msg_byte() -> i8 {
^entry:
  %m: ptr = globaladdr @msg @0
  %v: i8 = load nonatomic %m @0
  ret %v @0
}

module @dev() {
  func @k() -> ptr {
  ^entry:
    %a: ptr = funcaddr @k @0
    ret %a @0
  }

}

locs {
  @0 = unknown
}
