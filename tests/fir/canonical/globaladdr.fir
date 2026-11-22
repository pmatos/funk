global @msg() size(8) align(1) const units(104, 105, 0) {
}

global @table() size(24) align(8) addr(@msg) addr(@msg, 1) addr(@counter) {
}

global @counter() size(4) align(4) units(7) {
}

global @pad() size(16) align(8) units(1) {
}

func @msg_unit(%i: i64) -> i8 {
^entry:
  %m: ptr = globaladdr @msg @0
  %p: ptr = ptradd %m, %i @0
  %v: i8 = load nonatomic %p @0
  ret %v @0
}

func @follow(%i: i64) -> i8 {
^entry:
  %t: ptr = globaladdr @table @0
  %k: i64 = const 8 @0
  %o: i64 = mul %i, %k @0
  %e: ptr = ptradd %t, %o @0
  %p: ptr = load nonatomic %e @0
  %v: i8 = load nonatomic %p @0
  ret %v @0
}

func @bump(%x: i32) -> i32 {
^entry:
  %t: ptr = globaladdr @table @0
  %k: i64 = const 16 @0
  %e: ptr = ptradd %t, %k @0
  %c: ptr = load nonatomic %e @0
  %v: i32 = load nonatomic %c @0
  %s: i32 = add %v, %x @0
  %d: ptr = globaladdr @counter @0
  store nonatomic %s, %d @0
  %r: i32 = load nonatomic %d @0
  ret %r @0
}

func @write_msg(%x: i8) {
^entry:
  %m: ptr = globaladdr @msg @0
  store nonatomic %x, %m @0
  ret @0
}

func @read_past(%i: i64) -> i64 {
^entry:
  %t: ptr = globaladdr @pad @0
  %p: ptr = ptradd %t, %i @0
  %v: i64 = load nonatomic %p @0
  ret %v @0
}

func @addresses() -> ptr, ptr, ptr {
^entry:
  %a: ptr = globaladdr @msg @0
  %b: ptr = globaladdr @table @0
  %c: ptr = globaladdr @counter @0
  ret %a, %b, %c @0
}

locs {
  @0 = unknown
}
