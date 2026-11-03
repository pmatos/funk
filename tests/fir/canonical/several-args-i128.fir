func @spill0(%p0: i128, %p1: i64, %p2: i64, %p3: i64, %p4: i64) -> i128, i8, i128 {
^entry:
  %acc0: i128 = const 0 @0
  %k: i128 = const 1000003 @0
  %m0: i128 = mul %acc0, %k @0
  %acc1: i128 = add %m0, %p0 @0
  %x1: i128 = sext %p1 @0
  %m1: i128 = mul %acc1, %k @0
  %acc2: i128 = add %m1, %x1 @0
  %x2: i128 = sext %p2 @0
  %m2: i128 = mul %acc2, %k @0
  %acc3: i128 = add %m2, %x2 @0
  %x3: i128 = sext %p3 @0
  %m3: i128 = mul %acc3, %k @0
  %acc4: i128 = add %m3, %x3 @0
  %x4: i128 = sext %p4 @0
  %m4: i128 = mul %acc4, %k @0
  %acc5: i128 = add %m4, %x4 @0
  %t: i8 = trunc %acc5 @0
  ret %acc5, %t, %p0 @0
}

func @spill_call0(%p0: i64, %p1: i64, %p2: i64, %p3: i64, %p4: i128) -> i128, i8, i128 {
^entry:
  %one0: i64 = const 1 @0
  %q0: i64 = add %p0, %one0 @0
  %one1: i64 = const 1 @0
  %q1: i64 = add %p1, %one1 @0
  %one2: i64 = const 1 @0
  %q2: i64 = add %p2, %one2 @0
  %one3: i64 = const 1 @0
  %q3: i64 = add %p3, %one3 @0
  %one4: i128 = const 1 @0
  %q4: i128 = add %p4, %one4 @0
  %a: i128, %t: i8, %l: i128 = call @spill0 %q4, %q3, %q2, %q1, %q0 @0
  %s: i128 = add %a, %l @0
  ret %l, %t, %s @0
}

func @spill1(%p0: i128, %p1: i128, %p2: i128) -> i128, i8, i128 {
^entry:
  %acc0: i128 = const 0 @0
  %k: i128 = const 1000003 @0
  %m0: i128 = mul %acc0, %k @0
  %acc1: i128 = add %m0, %p0 @0
  %m1: i128 = mul %acc1, %k @0
  %acc2: i128 = add %m1, %p1 @0
  %m2: i128 = mul %acc2, %k @0
  %acc3: i128 = add %m2, %p2 @0
  %t: i8 = trunc %acc3 @0
  ret %acc3, %t, %p2 @0
}

func @spill_call1(%p0: i128, %p1: i128, %p2: i128) -> i128, i8, i128 {
^entry:
  %one0: i128 = const 1 @0
  %q0: i128 = add %p0, %one0 @0
  %one1: i128 = const 1 @0
  %q1: i128 = add %p1, %one1 @0
  %one2: i128 = const 1 @0
  %q2: i128 = add %p2, %one2 @0
  %a: i128, %t: i8, %l: i128 = call @spill1 %q2, %q1, %q0 @0
  %s: i128 = add %a, %l @0
  ret %l, %t, %s @0
}

func @spill2(%p0: i128, %p1: i128, %p2: i128, %p3: i64) -> i128, i8, i128 {
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
  %t: i8 = trunc %acc4 @0
  ret %acc4, %t, %p2 @0
}

func @spill_call2(%p0: i64, %p1: i128, %p2: i128, %p3: i128) -> i128, i8, i128 {
^entry:
  %one0: i64 = const 1 @0
  %q0: i64 = add %p0, %one0 @0
  %one1: i128 = const 1 @0
  %q1: i128 = add %p1, %one1 @0
  %one2: i128 = const 1 @0
  %q2: i128 = add %p2, %one2 @0
  %one3: i128 = const 1 @0
  %q3: i128 = add %p3, %one3 @0
  %a: i128, %t: i8, %l: i128 = call @spill2 %q3, %q2, %q1, %q0 @0
  %s: i128 = add %a, %l @0
  ret %l, %t, %s @0
}

func @spill3(%p0: i128, %p1: i64, %p2: i64, %p3: i64, %p4: i64, %p5: i64) -> i128, i8, i128 {
^entry:
  %acc0: i128 = const 0 @0
  %k: i128 = const 1000003 @0
  %m0: i128 = mul %acc0, %k @0
  %acc1: i128 = add %m0, %p0 @0
  %x1: i128 = sext %p1 @0
  %m1: i128 = mul %acc1, %k @0
  %acc2: i128 = add %m1, %x1 @0
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
  %t: i8 = trunc %acc6 @0
  ret %acc6, %t, %p0 @0
}

func @spill_call3(%p0: i64, %p1: i64, %p2: i64, %p3: i64, %p4: i64, %p5: i128) -> i128, i8, i128 {
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
  %a: i128, %t: i8, %l: i128 = call @spill3 %q5, %q4, %q3, %q2, %q1, %q0 @0
  %s: i128 = add %a, %l @0
  ret %l, %t, %s @0
}

func @spill4(%p0: i128, %p1: i64, %p2: i128, %p3: i128) -> i128, i8, i128 {
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
  %m3: i128 = mul %acc3, %k @0
  %acc4: i128 = add %m3, %p3 @0
  %t: i8 = trunc %acc4 @0
  ret %acc4, %t, %p3 @0
}

func @spill_call4(%p0: i128, %p1: i128, %p2: i64, %p3: i128) -> i128, i8, i128 {
^entry:
  %one0: i128 = const 1 @0
  %q0: i128 = add %p0, %one0 @0
  %one1: i128 = const 1 @0
  %q1: i128 = add %p1, %one1 @0
  %one2: i64 = const 1 @0
  %q2: i64 = add %p2, %one2 @0
  %one3: i128 = const 1 @0
  %q3: i128 = add %p3, %one3 @0
  %a: i128, %t: i8, %l: i128 = call @spill4 %q3, %q2, %q1, %q0 @0
  %s: i128 = add %a, %l @0
  ret %l, %t, %s @0
}

func @spill5(%p0: i64, %p1: i128, %p2: i64, %p3: i64, %p4: i64, %p5: i64, %p6: i64, %p7: i64) -> i128, i8, i128 {
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
  %t: i8 = trunc %acc8 @0
  ret %acc8, %t, %p1 @0
}

func @spill_call5(%p0: i64, %p1: i64, %p2: i64, %p3: i64, %p4: i64, %p5: i64, %p6: i128, %p7: i64) -> i128, i8, i128 {
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
  %one6: i128 = const 1 @0
  %q6: i128 = add %p6, %one6 @0
  %one7: i64 = const 1 @0
  %q7: i64 = add %p7, %one7 @0
  %a: i128, %t: i8, %l: i128 = call @spill5 %q7, %q6, %q5, %q4, %q3, %q2, %q1, %q0 @0
  %s: i128 = add %a, %l @0
  ret %l, %t, %s @0
}

func @spill6(%p0: i128, %p1: i64, %p2: i128, %p3: i32, %p4: i128, %p5: i16, %p6: i128, %p7: i1) -> i128, i8, i128 {
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
  %t: i8 = trunc %acc8 @0
  ret %acc8, %t, %p6 @0
}

func @spill_call6(%p0: i1, %p1: i128, %p2: i16, %p3: i128, %p4: i32, %p5: i128, %p6: i64, %p7: i128) -> i128, i8, i128 {
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
  %a: i128, %t: i8, %l: i128 = call @spill6 %q7, %q6, %q5, %q4, %q3, %q2, %q1, %q0 @0
  %s: i128 = add %a, %l @0
  ret %l, %t, %s @0
}

func @fibs(%n: i64, %a: i128, %b: i128) -> i128, i64, i128 {
^entry:
  %zero: i64 = const 0 @0
  %done: i1 = icmp sle %n, %zero @0
  cond_br %done, ^base, ^step @0
^base:
  ret %a, %n, %b @0
^step:
  %one: i64 = const 1 @0
  %m: i64 = sub %n, %one @0
  %c: i128 = add %a, %b @0
  %x: i128, %k: i64, %y: i128 = call @fibs %m, %b, %c @0
  %k1: i64 = add %k, %one @0
  ret %x, %k1, %y @0
}

locs {
  @0 = unknown
}
