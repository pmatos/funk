func @none(%a: i64) {
^entry:
  %b: i64 = add %a, %a @0
  ret @0
}

func @call_none(%a: i64) -> i64 {
^entry:
  call @none %a @0
  ret %a @0
}

func @two(%a: i64, %b: i64) -> i64, i64 {
^entry:
  %s: i64 = add %a, %b @0
  ret %s, %a @0
}

func @three(%a: i64, %b: i64) -> i64, i64, i64 {
^entry:
  %d: i64 = sub %a, %b @0
  %s: i64 = add %a, %b @0
  ret %d, %s, %b @0
}

func @eight(%a: i64) -> i64, i64, i64, i64, i64, i64, i64, i64 {
^entry:
  %one: i64 = const 1 @0
  %a1: i64 = add %a, %one @0
  %a2: i64 = add %a1, %one @0
  %a3: i64 = add %a2, %one @0
  %a4: i64 = add %a3, %one @0
  %a5: i64 = add %a4, %one @0
  %a6: i64 = add %a5, %one @0
  %a7: i64 = add %a6, %one @0
  ret %a, %a1, %a2, %a3, %a4, %a5, %a6, %a7 @0
}

func @use(%a: i64, %b: i64) -> i64, i64, i64 {
^entry:
  %d: i64, %s: i64, %c: i64 = call @three %a, %b @0
  %x: i64, %y: i64 = call @two %d, %s @0
  %e0: i64, %e1: i64, %e2: i64, %e3: i64, %e4: i64, %e5: i64, %e6: i64, %e7: i64 = call @eight %y @0
  ret %x, %e7, %c @0
}

func @fibs(%n: i64) -> i64, i64 {
^entry:
  %zero: i64 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^base, ^rec @0
^base:
  %one: i64 = const 1 @0
  ret %zero, %one @0
^rec:
  %one1: i64 = const 1 @0
  %m: i64 = sub %n, %one1 @0
  %a: i64, %b: i64 = call @fibs %m @0
  %s: i64 = add %a, %b @0
  ret %b, %s @0
}

func @trib(%n: i64) -> i64, i64, i64 {
^entry:
  %zero: i64 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^base, ^rec @0
^base:
  %one: i64 = const 1 @0
  ret %zero, %zero, %one @0
^rec:
  %one1: i64 = const 1 @0
  %m: i64 = sub %n, %one1 @0
  %a: i64, %b: i64, %c: i64 = call @trib %m @0
  %ab: i64 = add %a, %b @0
  %s: i64 = add %ab, %c @0
  ret %b, %c, %s @0
}

func @even(%n: i64) -> i1, i64, i64 {
^entry:
  %zero: i64 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const true @0
  ret %r, %zero, %zero @0
^more:
  %one: i64 = const 1 @0
  %m: i64 = sub %n, %one @0
  %p: i1, %k: i64, %d: i64 = call @odd %m @0
  %k1: i64 = add %k, %one @0
  %two: i64 = const 2 @0
  %d2: i64 = add %d, %two @0
  ret %p, %k1, %d2 @0
}

func @odd(%n: i64) -> i1, i64, i64 {
^entry:
  %zero: i64 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const false @0
  ret %r, %zero, %zero @0
^more:
  %one: i64 = const 1 @0
  %m: i64 = sub %n, %one @0
  %p: i1, %k: i64, %d: i64 = call @even %m @0
  %k1: i64 = add %k, %one @0
  %two: i64 = const 2 @0
  %d2: i64 = add %d, %two @0
  ret %p, %k1, %d2 @0
}

func @poison(%a: i64) -> i64, i64, i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  ret %a, %p, %one @0
}

func @call_poison(%a: i64) -> i64, i64, i64 {
^entry:
  %x: i64, %y: i64, %z: i64 = call @poison %a @0
  ret %z, %y, %x @0
}

func @divmod(%a: i64, %b: i64) -> i64, i64, i64 {
^entry:
  %q: i64 = udiv %a, %b @0
  %r: i64 = urem %a, %b @0
  ret %q, %r, %b @0
}

func @call_divmod(%a: i64, %b: i64) -> i64, i64 {
^entry:
  %q: i64, %r: i64, %c: i64 = call @divmod %a, %b @0
  ret %r, %q @0
}

func @forever(%a: i64) -> i64, i64, i64 {
^entry:
  %x: i64, %y: i64, %z: i64 = call @forever %a @0
  ret %z, %y, %x @0
}

locs {
  @0 = unknown
}
