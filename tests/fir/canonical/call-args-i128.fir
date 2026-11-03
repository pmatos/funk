func @fold0(%p0: i128, %p1: i128, %p2: i128) -> i128 {
^entry:
  %acc0: i128 = const 0 @0
  %k: i128 = const 1000003 @0
  %m0: i128 = mul %acc0, %k @0
  %acc1: i128 = add %m0, %p0 @0
  %m1: i128 = mul %acc1, %k @0
  %acc2: i128 = add %m1, %p1 @0
  %m2: i128 = mul %acc2, %k @0
  %acc3: i128 = add %m2, %p2 @0
  ret %acc3 @0
}

func @call0(%p0: i128, %p1: i128, %p2: i128) -> i128 {
^entry:
  %one0: i128 = const 1 @0
  %q0: i128 = add %p0, %one0 @0
  %one1: i128 = const 1 @0
  %q1: i128 = add %p1, %one1 @0
  %one2: i128 = const 1 @0
  %q2: i128 = add %p2, %one2 @0
  %r: i128 = call @fold0 %q2, %q1, %q0 @0
  ret %r @0
}

func @fold1(%p0: i128, %p1: i128, %p2: i128, %p3: i128) -> i128 {
^entry:
  %acc0: i128 = const 0 @0
  %k: i128 = const 1000003 @0
  %m0: i128 = mul %acc0, %k @0
  %acc1: i128 = add %m0, %p0 @0
  %m1: i128 = mul %acc1, %k @0
  %acc2: i128 = add %m1, %p1 @0
  %m2: i128 = mul %acc2, %k @0
  %acc3: i128 = add %m2, %p2 @0
  %m3: i128 = mul %acc3, %k @0
  %acc4: i128 = add %m3, %p3 @0
  ret %acc4 @0
}

func @call1(%p0: i128, %p1: i128, %p2: i128, %p3: i128) -> i128 {
^entry:
  %one0: i128 = const 1 @0
  %q0: i128 = add %p0, %one0 @0
  %one1: i128 = const 1 @0
  %q1: i128 = add %p1, %one1 @0
  %one2: i128 = const 1 @0
  %q2: i128 = add %p2, %one2 @0
  %one3: i128 = const 1 @0
  %q3: i128 = add %p3, %one3 @0
  %r: i128 = call @fold1 %q3, %q2, %q1, %q0 @0
  ret %r @0
}

func @fold2(%p0: i64, %p1: i128, %p2: i64, %p3: i64, %p4: i64, %p5: i64, %p6: i64) -> i128 {
^entry:
  %acc0: i128 = const 0 @0
  %k: i128 = const 1000003 @0
  %x0: i128 = sext %p0 @0
  %m0: i128 = mul %acc0, %k @0
  %acc1: i128 = add %m0, %x0 @0
  %m1: i128 = mul %acc1, %k @0
  %acc2: i128 = add %m1, %p1 @0
  %x2: i128 = sext %p2 @0
  %m2: i128 = mul %acc2, %k @0
  %acc3: i128 = add %m2, %x2 @0
  %x3: i128 = sext %p3 @0
  %m3: i128 = mul %acc3, %k @0
  %acc4: i128 = add %m3, %x3 @0
  %x4: i128 = sext %p4 @0
  %m4: i128 = mul %acc4, %k @0
  %acc5: i128 = add %m4, %x4 @0
  %x5: i128 = sext %p5 @0
  %m5: i128 = mul %acc5, %k @0
  %acc6: i128 = add %m5, %x5 @0
  %x6: i128 = sext %p6 @0
  %m6: i128 = mul %acc6, %k @0
  %acc7: i128 = add %m6, %x6 @0
  ret %acc7 @0
}

func @call2(%p0: i64, %p1: i64, %p2: i64, %p3: i64, %p4: i64, %p5: i128, %p6: i64) -> i128 {
^entry:
  %one0: i64 = const 1 @0
  %q0: i64 = add %p0, %one0 @0
  %one1: i64 = const 1 @0
  %q1: i64 = add %p1, %one1 @0
  %one2: i64 = const 1 @0
  %q2: i64 = add %p2, %one2 @0
  %one3: i64 = const 1 @0
  %q3: i64 = add %p3, %one3 @0
  %one4: i64 = const 1 @0
  %q4: i64 = add %p4, %one4 @0
  %one5: i128 = const 1 @0
  %q5: i128 = add %p5, %one5 @0
  %one6: i64 = const 1 @0
  %q6: i64 = add %p6, %one6 @0
  %r: i128 = call @fold2 %q6, %q5, %q4, %q3, %q2, %q1, %q0 @0
  ret %r @0
}

func @fold3(%p0: i64, %p1: i128, %p2: i64, %p3: i64, %p4: i64, %p5: i64, %p6: i64, %p7: i64, %p8: i64) -> i128 {
^entry:
  %acc0: i128 = const 0 @0
  %k: i128 = const 1000003 @0
  %x0: i128 = sext %p0 @0
  %m0: i128 = mul %acc0, %k @0
  %acc1: i128 = add %m0, %x0 @0
  %m1: i128 = mul %acc1, %k @0
  %acc2: i128 = add %m1, %p1 @0
  %x2: i128 = sext %p2 @0
  %m2: i128 = mul %acc2, %k @0
  %acc3: i128 = add %m2, %x2 @0
  %x3: i128 = sext %p3 @0
  %m3: i128 = mul %acc3, %k @0
  %acc4: i128 = add %m3, %x3 @0
  %x4: i128 = sext %p4 @0
  %m4: i128 = mul %acc4, %k @0
  %acc5: i128 = add %m4, %x4 @0
  %x5: i128 = sext %p5 @0
  %m5: i128 = mul %acc5, %k @0
  %acc6: i128 = add %m5, %x5 @0
  %x6: i128 = sext %p6 @0
  %m6: i128 = mul %acc6, %k @0
  %acc7: i128 = add %m6, %x6 @0
  %x7: i128 = sext %p7 @0
  %m7: i128 = mul %acc7, %k @0
  %acc8: i128 = add %m7, %x7 @0
  %x8: i128 = sext %p8 @0
  %m8: i128 = mul %acc8, %k @0
  %acc9: i128 = add %m8, %x8 @0
  ret %acc9 @0
}

func @call3(%p0: i64, %p1: i64, %p2: i64, %p3: i64, %p4: i64, %p5: i64, %p6: i64, %p7: i128, %p8: i64) -> i128 {
^entry:
  %one0: i64 = const 1 @0
  %q0: i64 = add %p0, %one0 @0
  %one1: i64 = const 1 @0
  %q1: i64 = add %p1, %one1 @0
  %one2: i64 = const 1 @0
  %q2: i64 = add %p2, %one2 @0
  %one3: i64 = const 1 @0
  %q3: i64 = add %p3, %one3 @0
  %one4: i64 = const 1 @0
  %q4: i64 = add %p4, %one4 @0
  %one5: i64 = const 1 @0
  %q5: i64 = add %p5, %one5 @0
  %one6: i64 = const 1 @0
  %q6: i64 = add %p6, %one6 @0
  %one7: i128 = const 1 @0
  %q7: i128 = add %p7, %one7 @0
  %one8: i64 = const 1 @0
  %q8: i64 = add %p8, %one8 @0
  %r: i128 = call @fold3 %q8, %q7, %q6, %q5, %q4, %q3, %q2, %q1, %q0 @0
  ret %r @0
}

func @fold4(%p0: i128, %p1: i128, %p2: i128, %p3: i64) -> i128 {
^entry:
  %acc0: i128 = const 0 @0
  %k: i128 = const 1000003 @0
  %m0: i128 = mul %acc0, %k @0
  %acc1: i128 = add %m0, %p0 @0
  %m1: i128 = mul %acc1, %k @0
  %acc2: i128 = add %m1, %p1 @0
  %m2: i128 = mul %acc2, %k @0
  %acc3: i128 = add %m2, %p2 @0
  %x3: i128 = sext %p3 @0
  %m3: i128 = mul %acc3, %k @0
  %acc4: i128 = add %m3, %x3 @0
  ret %acc4 @0
}

func @call4(%p0: i64, %p1: i128, %p2: i128, %p3: i128) -> i128 {
^entry:
  %one0: i64 = const 1 @0
  %q0: i64 = add %p0, %one0 @0
  %one1: i128 = const 1 @0
  %q1: i128 = add %p1, %one1 @0
  %one2: i128 = const 1 @0
  %q2: i128 = add %p2, %one2 @0
  %one3: i128 = const 1 @0
  %q3: i128 = add %p3, %one3 @0
  %r: i128 = call @fold4 %q3, %q2, %q1, %q0 @0
  ret %r @0
}

func @fold5(%p0: i128, %p1: i8, %p2: i128, %p3: i64, %p4: i128, %p5: i64, %p6: i128, %p7: i64, %p8: i128) -> i128 {
^entry:
  %acc0: i128 = const 0 @0
  %k: i128 = const 1000003 @0
  %m0: i128 = mul %acc0, %k @0
  %acc1: i128 = add %m0, %p0 @0
  %x1: i128 = sext %p1 @0
  %m1: i128 = mul %acc1, %k @0
  %acc2: i128 = add %m1, %x1 @0
  %m2: i128 = mul %acc2, %k @0
  %acc3: i128 = add %m2, %p2 @0
  %x3: i128 = sext %p3 @0
  %m3: i128 = mul %acc3, %k @0
  %acc4: i128 = add %m3, %x3 @0
  %m4: i128 = mul %acc4, %k @0
  %acc5: i128 = add %m4, %p4 @0
  %x5: i128 = sext %p5 @0
  %m5: i128 = mul %acc5, %k @0
  %acc6: i128 = add %m5, %x5 @0
  %m6: i128 = mul %acc6, %k @0
  %acc7: i128 = add %m6, %p6 @0
  %x7: i128 = sext %p7 @0
  %m7: i128 = mul %acc7, %k @0
  %acc8: i128 = add %m7, %x7 @0
  %m8: i128 = mul %acc8, %k @0
  %acc9: i128 = add %m8, %p8 @0
  ret %acc9 @0
}

func @call5(%p0: i128, %p1: i64, %p2: i128, %p3: i64, %p4: i128, %p5: i64, %p6: i128, %p7: i8, %p8: i128) -> i128 {
^entry:
  %one0: i128 = const 1 @0
  %q0: i128 = add %p0, %one0 @0
  %one1: i64 = const 1 @0
  %q1: i64 = add %p1, %one1 @0
  %one2: i128 = const 1 @0
  %q2: i128 = add %p2, %one2 @0
  %one3: i64 = const 1 @0
  %q3: i64 = add %p3, %one3 @0
  %one4: i128 = const 1 @0
  %q4: i128 = add %p4, %one4 @0
  %one5: i64 = const 1 @0
  %q5: i64 = add %p5, %one5 @0
  %one6: i128 = const 1 @0
  %q6: i128 = add %p6, %one6 @0
  %one7: i8 = const 1 @0
  %q7: i8 = add %p7, %one7 @0
  %one8: i128 = const 1 @0
  %q8: i128 = add %p8, %one8 @0
  %r: i128 = call @fold5 %q8, %q7, %q6, %q5, %q4, %q3, %q2, %q1, %q0 @0
  ret %r @0
}

func @fold6(%p0: i128, %p1: i64, %p2: i128, %p3: i32, %p4: i128, %p5: i16, %p6: i128, %p7: i1) -> i128 {
^entry:
  %acc0: i128 = const 0 @0
  %k: i128 = const 1000003 @0
  %m0: i128 = mul %acc0, %k @0
  %acc1: i128 = add %m0, %p0 @0
  %x1: i128 = sext %p1 @0
  %m1: i128 = mul %acc1, %k @0
  %acc2: i128 = add %m1, %x1 @0
  %m2: i128 = mul %acc2, %k @0
  %acc3: i128 = add %m2, %p2 @0
  %x3: i128 = sext %p3 @0
  %m3: i128 = mul %acc3, %k @0
  %acc4: i128 = add %m3, %x3 @0
  %m4: i128 = mul %acc4, %k @0
  %acc5: i128 = add %m4, %p4 @0
  %x5: i128 = sext %p5 @0
  %m5: i128 = mul %acc5, %k @0
  %acc6: i128 = add %m5, %x5 @0
  %m6: i128 = mul %acc6, %k @0
  %acc7: i128 = add %m6, %p6 @0
  %x7: i128 = sext %p7 @0
  %m7: i128 = mul %acc7, %k @0
  %acc8: i128 = add %m7, %x7 @0
  ret %acc8 @0
}

func @call6(%p0: i1, %p1: i128, %p2: i16, %p3: i128, %p4: i32, %p5: i128, %p6: i64, %p7: i128) -> i128 {
^entry:
  %one0: i1 = const true @0
  %q0: i1 = add %p0, %one0 @0
  %one1: i128 = const 1 @0
  %q1: i128 = add %p1, %one1 @0
  %one2: i16 = const 1 @0
  %q2: i16 = add %p2, %one2 @0
  %one3: i128 = const 1 @0
  %q3: i128 = add %p3, %one3 @0
  %one4: i32 = const 1 @0
  %q4: i32 = add %p4, %one4 @0
  %one5: i128 = const 1 @0
  %q5: i128 = add %p5, %one5 @0
  %one6: i64 = const 1 @0
  %q6: i64 = add %p6, %one6 @0
  %one7: i128 = const 1 @0
  %q7: i128 = add %p7, %one7 @0
  %r: i128 = call @fold6 %q7, %q6, %q5, %q4, %q3, %q2, %q1, %q0 @0
  ret %r @0
}

locs {
  @0 = unknown
}
