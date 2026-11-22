func @through_memory(%x: i64) -> i64 {
^entry:
  %p: ptr = alloca stack i64 @0
  store nonatomic %x, %p @0
  %s: ptr = alloca stack i64 @0
  %a: i64 = ptr_expose %p @0
  store nonatomic %a, %s @0
  %b: i64 = load nonatomic %s @0
  %q: ptr = ptr_from_int %b @0
  %v: i64 = load nonatomic %q @0
  ret %v @0
}

func @put(%a: i64, %x: i32) {
^entry:
  %q: ptr = ptr_from_int %a @1
  store nonatomic %x, %q @1
  ret @1
}

func @through_call(%x: i32) -> i32 {
^entry:
  %p: ptr = alloca stack i32 @1
  %zero: i32 = const 0 @1
  store nonatomic %zero, %p @1
  %a: i64 = ptr_expose %p @1
  call @put %a, %x @1
  %v: i32 = load nonatomic %p @1
  ret %v @1
}

func @walk(%n: i32) -> i32 {
^entry:
  %p: ptr = alloca stack i32 4 @2
  %a: i64 = ptr_expose %p @2
  %zero: i64 = const 0 @2
  %four: i64 = const 4 @2
  %sixteen: i64 = const 16 @2
  br ^fill(%zero, %n) @2
^fill(%i: i64, %v: i32):
  %b: i64 = add %a, %i @2
  %q: ptr = ptr_from_int %b @2
  store nonatomic %v, %q @2
  %v1: i32 = add %v, %v @2
  %i1: i64 = add %i, %four @2
  %more: i1 = icmp ult %i1, %sixteen @2
  cond_br %more, ^fill(%i1, %v1), ^sum @2
^sum:
  %s0: i32 = load nonatomic %p @2
  %p1: ptr = ptradd %p, %four @2
  %s1: i32 = load nonatomic %p1 @2
  %eight: i64 = const 8 @2
  %p2: ptr = ptradd %p, %eight @2
  %s2: i32 = load nonatomic %p2 @2
  %twelve: i64 = const 12 @2
  %p3: ptr = ptradd %p, %twelve @2
  %s3: i32 = load nonatomic %p3 @2
  %t0: i32 = add %s0, %s1 @2
  %t1: i32 = add %s2, %s3 @2
  %t: i32 = add %t0, %t1 @2
  ret %t @2
}

func @aligned() -> i64, i1 {
^entry:
  %p: ptr = alloca stack i8 align(64) @3
  %a: i64 = ptr_expose %p @3
  %sixty_four: i64 = const 64 @3
  %r: i64 = urem %a, %sixty_four @3
  %zero: i64 = const 0 @3
  %z: i1 = icmp eq %a, %zero @3
  ret %r, %z @3
}

locs {
  @0 = unknown
  @1 = unknown
  @2 = unknown
  @3 = unknown
}
