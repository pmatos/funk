func @none(%a: i16) {
^entry:
  %b: i16 = add %a, %a @0
  ret @0
}

func @call_none(%a: i16) -> i16 {
^entry:
  call @none %a @0
  ret %a @0
}

func @two(%a: i16, %b: i16) -> i16, i16 {
^entry:
  %s: i16 = add %a, %b @0
  ret %s, %a @0
}

func @three(%a: i16, %b: i16) -> i16, i16, i16 {
^entry:
  %d: i16 = sub %a, %b @0
  %s: i16 = add %a, %b @0
  ret %d, %s, %b @0
}

func @eight(%a: i16) -> i16, i16, i16, i16, i16, i16, i16, i16 {
^entry:
  %one: i16 = const 1 @0
  %a1: i16 = add %a, %one @0
  %a2: i16 = add %a1, %one @0
  %a3: i16 = add %a2, %one @0
  %a4: i16 = add %a3, %one @0
  %a5: i16 = add %a4, %one @0
  %a6: i16 = add %a5, %one @0
  %a7: i16 = add %a6, %one @0
  ret %a, %a1, %a2, %a3, %a4, %a5, %a6, %a7 @0
}

func @use(%a: i16, %b: i16) -> i16, i16, i16 {
^entry:
  %d: i16, %s: i16, %c: i16 = call @three %a, %b @0
  %x: i16, %y: i16 = call @two %d, %s @0
  %e0: i16, %e1: i16, %e2: i16, %e3: i16, %e4: i16, %e5: i16, %e6: i16, %e7: i16 = call @eight %y @0
  ret %x, %e7, %c @0
}

func @fibs(%n: i16) -> i16, i16 {
^entry:
  %zero: i16 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^base, ^rec @0
^base:
  %one: i16 = const 1 @0
  ret %zero, %one @0
^rec:
  %one1: i16 = const 1 @0
  %m: i16 = sub %n, %one1 @0
  %a: i16, %b: i16 = call @fibs %m @0
  %s: i16 = add %a, %b @0
  ret %b, %s @0
}

func @trib(%n: i16) -> i16, i16, i16 {
^entry:
  %zero: i16 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^base, ^rec @0
^base:
  %one: i16 = const 1 @0
  ret %zero, %zero, %one @0
^rec:
  %one1: i16 = const 1 @0
  %m: i16 = sub %n, %one1 @0
  %a: i16, %b: i16, %c: i16 = call @trib %m @0
  %ab: i16 = add %a, %b @0
  %s: i16 = add %ab, %c @0
  ret %b, %c, %s @0
}

func @even(%n: i16) -> i1, i16, i16 {
^entry:
  %zero: i16 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const true @0
  ret %r, %zero, %zero @0
^more:
  %one: i16 = const 1 @0
  %m: i16 = sub %n, %one @0
  %p: i1, %k: i16, %d: i16 = call @odd %m @0
  %k1: i16 = add %k, %one @0
  %two: i16 = const 2 @0
  %d2: i16 = add %d, %two @0
  ret %p, %k1, %d2 @0
}

func @odd(%n: i16) -> i1, i16, i16 {
^entry:
  %zero: i16 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const false @0
  ret %r, %zero, %zero @0
^more:
  %one: i16 = const 1 @0
  %m: i16 = sub %n, %one @0
  %p: i1, %k: i16, %d: i16 = call @even %m @0
  %k1: i16 = add %k, %one @0
  %two: i16 = const 2 @0
  %d2: i16 = add %d, %two @0
  ret %p, %k1, %d2 @0
}

func @poison(%a: i16) -> i16, i16, i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  ret %a, %p, %one @0
}

func @call_poison(%a: i16) -> i16, i16, i16 {
^entry:
  %x: i16, %y: i16, %z: i16 = call @poison %a @0
  ret %z, %y, %x @0
}

func @divmod(%a: i16, %b: i16) -> i16, i16, i16 {
^entry:
  %q: i16 = udiv %a, %b @0
  %r: i16 = urem %a, %b @0
  ret %q, %r, %b @0
}

func @call_divmod(%a: i16, %b: i16) -> i16, i16 {
^entry:
  %q: i16, %r: i16, %c: i16 = call @divmod %a, %b @0
  ret %r, %q @0
}

func @forever(%a: i16) -> i16, i16, i16 {
^entry:
  %x: i16, %y: i16, %z: i16 = call @forever %a @0
  ret %z, %y, %x @0
}

locs {
  @0 = unknown
}
