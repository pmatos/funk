func @first(%p0: i128, %p1: i8, %p2: i1) -> i128, i8, i1 {
^entry:
  %c0: i128 = const 1 @0
  %r0: i128 = add %p0, %c0 @0
  %c1: i8 = const 1 @0
  %r1: i8 = add %p1, %c1 @0
  %c2: i1 = const true @0
  %r2: i1 = add %p2, %c2 @0
  ret %r0, %r1, %r2 @0
}

func @use_first(%p0: i128, %p1: i8, %p2: i1) -> i1, i8, i128 {
^entry:
  %r0: i128, %r1: i8, %r2: i1 = call @first %p0, %p1, %p2 @0
  %s0: i128 = add %r0, %r0 @0
  %c1: i8 = const 1 @0
  %s1: i8 = add %r1, %c1 @0
  %c2: i1 = const true @0
  %s2: i1 = add %r2, %c2 @0
  ret %s2, %s1, %s0 @0
}

func @middle(%p0: i1, %p1: i128, %p2: i8) -> i1, i128, i8 {
^entry:
  %c0: i1 = const true @0
  %r0: i1 = add %p0, %c0 @0
  %c1: i128 = const 1 @0
  %r1: i128 = add %p1, %c1 @0
  %c2: i8 = const 1 @0
  %r2: i8 = add %p2, %c2 @0
  ret %r0, %r1, %r2 @0
}

func @use_middle(%p0: i1, %p1: i128, %p2: i8) -> i8, i128, i1 {
^entry:
  %r0: i1, %r1: i128, %r2: i8 = call @middle %p0, %p1, %p2 @0
  %c0: i1 = const true @0
  %s0: i1 = add %r0, %c0 @0
  %s1: i128 = add %r1, %r1 @0
  %c2: i8 = const 1 @0
  %s2: i8 = add %r2, %c2 @0
  ret %s2, %s1, %s0 @0
}

func @last(%p0: i64, %p1: i16, %p2: i128) -> i64, i16, i128 {
^entry:
  %c0: i64 = const 1 @0
  %r0: i64 = add %p0, %c0 @0
  %c1: i16 = const 1 @0
  %r1: i16 = add %p1, %c1 @0
  %c2: i128 = const 1 @0
  %r2: i128 = add %p2, %c2 @0
  ret %r0, %r1, %r2 @0
}

func @use_last(%p0: i64, %p1: i16, %p2: i128) -> i128, i16, i64 {
^entry:
  %r0: i64, %r1: i16, %r2: i128 = call @last %p0, %p1, %p2 @0
  %c0: i64 = const 1 @0
  %s0: i64 = add %r0, %c0 @0
  %c1: i16 = const 1 @0
  %s1: i16 = add %r1, %c1 @0
  %s2: i128 = add %r2, %r2 @0
  ret %s2, %s1, %s0 @0
}

func @four(%p0: i1, %p1: i128, %p2: i8, %p3: i16) -> i1, i128, i8, i16 {
^entry:
  %c0: i1 = const true @0
  %r0: i1 = add %p0, %c0 @0
  %c1: i128 = const 1 @0
  %r1: i128 = add %p1, %c1 @0
  %c2: i8 = const 1 @0
  %r2: i8 = add %p2, %c2 @0
  %c3: i16 = const 1 @0
  %r3: i16 = add %p3, %c3 @0
  ret %r0, %r1, %r2, %r3 @0
}

func @use_four(%p0: i1, %p1: i128, %p2: i8, %p3: i16) -> i16, i8, i128, i1 {
^entry:
  %r0: i1, %r1: i128, %r2: i8, %r3: i16 = call @four %p0, %p1, %p2, %p3 @0
  %c0: i1 = const true @0
  %s0: i1 = add %r0, %c0 @0
  %s1: i128 = add %r1, %r1 @0
  %c2: i8 = const 1 @0
  %s2: i8 = add %r2, %c2 @0
  %c3: i16 = const 1 @0
  %s3: i16 = add %r3, %c3 @0
  ret %s3, %s2, %s1, %s0 @0
}

func @twice(%p0: i128, %p1: i32, %p2: i128, %p3: i1) -> i128, i32, i128, i1 {
^entry:
  %c0: i128 = const 1 @0
  %r0: i128 = add %p0, %c0 @0
  %c1: i32 = const 1 @0
  %r1: i32 = add %p1, %c1 @0
  %c2: i128 = const 1 @0
  %r2: i128 = add %p2, %c2 @0
  %c3: i1 = const true @0
  %r3: i1 = add %p3, %c3 @0
  ret %r0, %r1, %r2, %r3 @0
}

func @use_twice(%p0: i128, %p1: i32, %p2: i128, %p3: i1) -> i1, i128, i32, i128 {
^entry:
  %r0: i128, %r1: i32, %r2: i128, %r3: i1 = call @twice %p0, %p1, %p2, %p3 @0
  %s0: i128 = add %r0, %r0 @0
  %c1: i32 = const 1 @0
  %s1: i32 = add %r1, %c1 @0
  %s2: i128 = add %r2, %r2 @0
  %c3: i1 = const true @0
  %s3: i1 = add %r3, %c3 @0
  ret %s3, %s2, %s1, %s0 @0
}

func @poison(%x: i128, %a: i8) -> i8, i128, i1 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %x, %one @0
  %t: i1 = const true @0
  ret %a, %p, %t @0
}

func @call_poison(%x: i128, %a: i8) -> i1, i128, i8 {
^entry:
  %r: i8, %p: i128, %t: i1 = call @poison %x, %a @0
  ret %t, %p, %r @0
}

func @poison_narrow(%x: i128, %a: i8) -> i128, i8, i128 {
^entry:
  %one: i8 = const 1 @0
  %q: i8 = add nsw %a, %one @0
  %k: i128 = const 18446744073709551615 @0
  %y: i128 = add %x, %k @0
  ret %x, %q, %y @0
}

func @call_poison_narrow(%x: i128, %a: i8) -> i8, i128, i128 {
^entry:
  %y: i128, %q: i8, %z: i128 = call @poison_narrow %x, %a @0
  ret %q, %z, %y @0
}

func @frozen(%x: i128) -> i128, i8, i128 {
^entry:
  %big: i128 = const 170141183460469231731687303715884105727 @0
  %p: i128 = add nsw %x, %big @0
  %f: i128 = freeze %p @0
  %c: i8 = const 7 @0
  ret %f, %c, %f @0
}

func @frozen_use(%x: i128) -> i128, i8 {
^entry:
  %a: i128, %c: i8, %b: i128 = call @frozen %x @0
  %d: i128 = sub %a, %b @0
  ret %d, %c @0
}

locs {
  @0 = unknown
}
