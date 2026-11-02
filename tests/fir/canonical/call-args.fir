func @mix7(%a: i8, %b: i1, %c: i64, %d: i32, %e: i16, %f: i8, %g: i1) -> i64 {
^entry:
  %k: i64 = const 1000003 @0
  %a64: i64 = sext %a @0
  %b64: i64 = sext %b @0
  %m1: i64 = mul %a64, %k @0
  %s1: i64 = add %m1, %b64 @0
  %m2: i64 = mul %s1, %k @0
  %s2: i64 = add %m2, %c @0
  %d64: i64 = sext %d @0
  %m3: i64 = mul %s2, %k @0
  %s3: i64 = add %m3, %d64 @0
  %e64: i64 = sext %e @0
  %m4: i64 = mul %s3, %k @0
  %s4: i64 = add %m4, %e64 @0
  %f64: i64 = sext %f @0
  %m5: i64 = mul %s4, %k @0
  %s5: i64 = add %m5, %f64 @0
  %g64: i64 = sext %g @0
  %m6: i64 = mul %s5, %k @0
  %s6: i64 = add %m6, %g64 @0
  ret %s6 @0
}

func @call7(%a: i1, %b: i8, %c: i16, %d: i32, %e: i64, %f: i1, %g: i8) -> i64 {
^entry:
  %one1: i1 = const true @0
  %one8: i8 = const 1 @0
  %one16: i16 = const 1 @0
  %one32: i32 = const 1 @0
  %one64: i64 = const 1 @0
  %a1: i1 = add %a, %one1 @0
  %b1: i8 = add %b, %one8 @0
  %c1: i16 = add %c, %one16 @0
  %d1: i32 = add %d, %one32 @0
  %e1: i64 = add %e, %one64 @0
  %f1: i1 = add %f, %one1 @0
  %g1: i8 = add %g, %one8 @0
  %r: i64 = call @mix7 %g1, %f1, %e1, %d1, %c1, %b1, %a1 @0
  ret %r @0
}

func @mix8(%a: i32, %b: i16, %c: i8, %d: i1, %e: i8, %f: i16, %g: i32, %h: i64) -> i64 {
^entry:
  %k: i64 = const 1000003 @0
  %a64: i64 = sext %a @0
  %b64: i64 = sext %b @0
  %m1: i64 = mul %a64, %k @0
  %s1: i64 = add %m1, %b64 @0
  %c64: i64 = sext %c @0
  %m2: i64 = mul %s1, %k @0
  %s2: i64 = add %m2, %c64 @0
  %d64: i64 = sext %d @0
  %m3: i64 = mul %s2, %k @0
  %s3: i64 = add %m3, %d64 @0
  %e64: i64 = sext %e @0
  %m4: i64 = mul %s3, %k @0
  %s4: i64 = add %m4, %e64 @0
  %f64: i64 = sext %f @0
  %m5: i64 = mul %s4, %k @0
  %s5: i64 = add %m5, %f64 @0
  %g64: i64 = sext %g @0
  %m6: i64 = mul %s5, %k @0
  %s6: i64 = add %m6, %g64 @0
  %m7: i64 = mul %s6, %k @0
  %s7: i64 = add %m7, %h @0
  ret %s7 @0
}

func @call8(%a: i64, %b: i32, %c: i16, %d: i8, %e: i1, %f: i8, %g: i16, %h: i32) -> i64 {
^entry:
  %one1: i1 = const true @0
  %one8: i8 = const 1 @0
  %one16: i16 = const 1 @0
  %one32: i32 = const 1 @0
  %one64: i64 = const 1 @0
  %a1: i64 = add %a, %one64 @0
  %b1: i32 = add %b, %one32 @0
  %c1: i16 = add %c, %one16 @0
  %d1: i8 = add %d, %one8 @0
  %e1: i1 = add %e, %one1 @0
  %f1: i8 = add %f, %one8 @0
  %g1: i16 = add %g, %one16 @0
  %h1: i32 = add %h, %one32 @0
  %r: i64 = call @mix8 %h1, %g1, %f1, %e1, %d1, %c1, %b1, %a1 @0
  ret %r @0
}

locs {
  @0 = unknown
}
