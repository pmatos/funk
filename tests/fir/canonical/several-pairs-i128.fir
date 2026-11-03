func @wide(%p0: i128, %p1: i64) -> i128, i64 {
^entry:
  %c0: i128 = const 1 @0
  %r0: i128 = add %p0, %c0 @0
  %c1: i64 = const 1 @0
  %r1: i64 = add %p1, %c1 @0
  ret %r0, %r1 @0
}

func @use_wide(%p0: i128, %p1: i64) -> i64, i128 {
^entry:
  %r0: i128, %r1: i64 = call @wide %p0, %p1 @0
  %s0: i128 = add %r0, %r0 @0
  %c1: i64 = const 1 @0
  %s1: i64 = add %r1, %c1 @0
  ret %s1, %s0 @0
}

func @narrow(%p0: i64, %p1: i128) -> i64, i128 {
^entry:
  %c0: i64 = const 1 @0
  %r0: i64 = add %p0, %c0 @0
  %c1: i128 = const 1 @0
  %r1: i128 = add %p1, %c1 @0
  ret %r0, %r1 @0
}

func @use_narrow(%p0: i64, %p1: i128) -> i128, i64 {
^entry:
  %r0: i64, %r1: i128 = call @narrow %p0, %p1 @0
  %c0: i64 = const 1 @0
  %s0: i64 = add %r0, %c0 @0
  %s1: i128 = add %r1, %r1 @0
  ret %s1, %s0 @0
}

func @two(%p0: i128, %p1: i128) -> i128, i128 {
^entry:
  %c0: i128 = const 1 @0
  %r0: i128 = add %p0, %c0 @0
  %c1: i128 = const 1 @0
  %r1: i128 = add %p1, %c1 @0
  ret %r0, %r1 @0
}

func @use_two(%p0: i128, %p1: i128) -> i128, i128 {
^entry:
  %r0: i128, %r1: i128 = call @two %p0, %p1 @0
  %s0: i128 = add %r0, %r0 @0
  %s1: i128 = add %r1, %r1 @0
  ret %s1, %s0 @0
}

func @chain(%x: i128, %a: i64) -> i64, i128, i128 {
^entry:
  %p: i128, %q: i64 = call @wide %x, %a @0
  %r: i64, %s: i128 = call @narrow %q, %p @0
  %t: i128, %u: i128 = call @two %s, %p @0
  ret %r, %t, %u @0
}

func @divmod(%x: i128, %a: i64, %b: i64) -> i64, i128, i64 {
^entry:
  %q: i64 = udiv %a, %b @0
  %r: i64 = urem %a, %b @0
  ret %q, %x, %r @0
}

func @call_divmod(%x: i128, %a: i64, %b: i64) -> i128, i64 {
^entry:
  %q: i64, %y: i128, %r: i64 = call @divmod %x, %a, %b @0
  ret %y, %r @0
}

func @forever(%x: i128) -> i128, i8, i128 {
^entry:
  %a: i128, %c: i8, %b: i128 = call @forever %x @0
  ret %b, %c, %a @0
}

locs {
  @0 = unknown
}
