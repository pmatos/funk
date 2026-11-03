func @mixed(%p0: i1, %p1: i8, %p2: i16, %p3: i32, %p4: i64) -> i64, i1, i16, i8, i32, i1, i64 {
^entry:
  %t: i1 = const true @0
  %na: i1 = add %p0, %t @0
  %one: i8 = const 1 @0
  %b1: i8 = add %p1, %one @0
  %m: i16 = const -1 @0
  %c1: i16 = add %p2, %m @0
  ret %p4, %na, %c1, %b1, %p3, %p0, %p4 @0
}

func @flip(%x: i16, %y: i1) -> i1, i16 {
^entry:
  ret %y, %x @0
}

func @mixed_use(%p0: i1, %p1: i8, %p2: i16, %p3: i32, %p4: i64) -> i8, i1, i16, i64, i1 {
^entry:
  %r0: i64, %r1: i1, %r2: i16, %r3: i8, %r4: i32, %r5: i1, %r6: i64 = call @mixed %p0, %p1, %p2, %p3, %p4 @0
  %f0: i1, %f1: i16 = call @flip %r2, %r1 @0
  %zero: i8 = const 0 @0
  %neg: i1 = icmp slt %r3, %zero @0
  %w: i64 = sext %r4 @0
  %sum: i64 = add %w, %r6 @0
  ret %r3, %neg, %f1, %sum, %f0 @0
}

func @spread(%p0: i1, %p1: i8, %p2: i16, %p3: i32, %p4: i64, %p5: i1, %p6: i8, %p7: i16) -> i16, i8, i1, i64, i32 {
^entry:
  %c8: i8 = const 1 @0
  %c16: i16 = const 1 @0
  %c64: i64 = const 1 @0
  %q7: i16 = add %p7, %c16 @0
  %q6: i8 = add %p6, %c8 @0
  %q4: i64 = add %p4, %c64 @0
  ret %q7, %q6, %p5, %q4, %p3 @0
}

func @spread_call(%p0: i1, %p1: i8, %p2: i16, %p3: i32, %p4: i64, %p5: i1, %p6: i8, %p7: i16) -> i32, i64, i1, i8, i16 {
^entry:
  %r0: i16, %r1: i8, %r2: i1, %r3: i64, %r4: i32 = call @spread %p0, %p1, %p2, %p3, %p4, %p5, %p6, %p7 @0
  ret %r4, %r3, %r2, %r1, %r0 @0
}

func @six(%p0: i8, %p1: i16, %p2: i32, %p3: i64, %p4: i1, %p5: i64) -> i64, i8, i1 {
^entry:
  ret %p5, %p0, %p4 @0
}

func @six_call(%p0: i8, %p1: i16, %p2: i32, %p3: i64, %p4: i1, %p5: i64) -> i1, i64, i8, i64 {
^entry:
  %a: i64, %b: i8, %c: i1 = call @six %p0, %p1, %p2, %p3, %p4, %p5 @0
  %d: i64, %e: i8, %f: i1 = call @six %b, %p1, %p2, %a, %c, %p3 @0
  ret %f, %d, %e, %a @0
}

locs {
  @0 = unknown
}
