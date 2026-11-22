func @round_trip(%x: i32) -> i32 {
^entry:
  %p: ptr = alloca stack i32 @0
  store nonatomic %x, %p @0
  %a: i64 = ptr_expose %p @0
  %q: ptr = ptr_from_int %a @0
  %v: i32 = load nonatomic %q @0
  ret %v @0
}

func @at(%x: i32, %y: i32, %k: i64) -> i32 {
^entry:
  %p: ptr = alloca stack i32 2 @1
  store nonatomic %x, %p @1
  %four: i64 = const 4 @1
  %p1: ptr = ptradd %p, %four @1
  store nonatomic %y, %p1 @1
  %a: i64 = ptr_expose %p @1
  %b: i64 = add %a, %k @1
  %q: ptr = ptr_from_int %b @1
  %v: i32 = load nonatomic %q @1
  ret %v @1
}

func @distance() -> i64 {
^entry:
  %p: ptr = alloca stack i32 2 @2
  %four: i64 = const 4 @2
  %p1: ptr = ptradd %p, %four @2
  %a: i64 = ptr_expose %p @2
  %b: i64 = ptr_expose %p1 @2
  %d: i64 = sub %b, %a @2
  ret %d @2
}

func @never(%a: i64) -> i32 {
^entry:
  %p: ptr = alloca stack i32 @3
  %x: i32 = const 1 @3
  store nonatomic %x, %p @3
  %q: ptr = ptr_from_int %a @3
  %v: i32 = load nonatomic %q @3
  ret %v @3
}

func @back(%a: i64) -> i64 {
^entry:
  %q: ptr = ptr_from_int %a @4
  %b: i64 = ptr_expose %q @4
  ret %b @4
}

locs {
  @0 = unknown
  @1 = unknown
  @2 = unknown
  @3 = unknown
  @4 = unknown
}
