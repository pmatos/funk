func @none(%a: i7) {
^entry:
  %b: i7 = add %a, %a @0
  ret @0
}

func @call_none(%a: i7) -> i7 {
^entry:
  call @none %a @0
  ret %a @0
}

func @two(%a: i7, %b: i7) -> i7, i7 {
^entry:
  %s: i7 = add %a, %b @0
  ret %s, %a @0
}

func @three(%a: i7, %b: i7) -> i7, i7, i7 {
^entry:
  %d: i7 = sub %a, %b @0
  %s: i7 = add %a, %b @0
  ret %d, %s, %b @0
}

func @eight(%a: i7) -> i7, i7, i7, i7, i7, i7, i7, i7 {
^entry:
  %one: i7 = const 1 @0
  %a1: i7 = add %a, %one @0
  %a2: i7 = add %a1, %one @0
  %a3: i7 = add %a2, %one @0
  %a4: i7 = add %a3, %one @0
  %a5: i7 = add %a4, %one @0
  %a6: i7 = add %a5, %one @0
  %a7: i7 = add %a6, %one @0
  ret %a, %a1, %a2, %a3, %a4, %a5, %a6, %a7 @0
}

func @use(%a: i7, %b: i7) -> i7, i7, i7 {
^entry:
  %d: i7, %s: i7, %c: i7 = call @three %a, %b @0
  %x: i7, %y: i7 = call @two %d, %s @0
  %e0: i7, %e1: i7, %e2: i7, %e3: i7, %e4: i7, %e5: i7, %e6: i7, %e7: i7 = call @eight %y @0
  ret %x, %e7, %c @0
}

func @fibs(%n: i7) -> i7, i7 {
^entry:
  %zero: i7 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^base, ^rec @0
^base:
  %one: i7 = const 1 @0
  ret %zero, %one @0
^rec:
  %one1: i7 = const 1 @0
  %m: i7 = sub %n, %one1 @0
  %a: i7, %b: i7 = call @fibs %m @0
  %s: i7 = add %a, %b @0
  ret %b, %s @0
}

func @trib(%n: i7) -> i7, i7, i7 {
^entry:
  %zero: i7 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^base, ^rec @0
^base:
  %one: i7 = const 1 @0
  ret %zero, %zero, %one @0
^rec:
  %one1: i7 = const 1 @0
  %m: i7 = sub %n, %one1 @0
  %a: i7, %b: i7, %c: i7 = call @trib %m @0
  %ab: i7 = add %a, %b @0
  %s: i7 = add %ab, %c @0
  ret %b, %c, %s @0
}

func @even(%n: i7) -> i1, i7, i7 {
^entry:
  %zero: i7 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const true @0
  ret %r, %zero, %zero @0
^more:
  %one: i7 = const 1 @0
  %m: i7 = sub %n, %one @0
  %p: i1, %k: i7, %d: i7 = call @odd %m @0
  %k1: i7 = add %k, %one @0
  %two: i7 = const 2 @0
  %d2: i7 = add %d, %two @0
  ret %p, %k1, %d2 @0
}

func @odd(%n: i7) -> i1, i7, i7 {
^entry:
  %zero: i7 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const false @0
  ret %r, %zero, %zero @0
^more:
  %one: i7 = const 1 @0
  %m: i7 = sub %n, %one @0
  %p: i1, %k: i7, %d: i7 = call @even %m @0
  %k1: i7 = add %k, %one @0
  %two: i7 = const 2 @0
  %d2: i7 = add %d, %two @0
  ret %p, %k1, %d2 @0
}

func @poison(%a: i7) -> i7, i7, i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  ret %a, %p, %one @0
}

func @call_poison(%a: i7) -> i7, i7, i7 {
^entry:
  %x: i7, %y: i7, %z: i7 = call @poison %a @0
  ret %z, %y, %x @0
}

func @divmod(%a: i7, %b: i7) -> i7, i7, i7 {
^entry:
  %q: i7 = udiv %a, %b @0
  %r: i7 = urem %a, %b @0
  ret %q, %r, %b @0
}

func @call_divmod(%a: i7, %b: i7) -> i7, i7 {
^entry:
  %q: i7, %r: i7, %c: i7 = call @divmod %a, %b @0
  ret %r, %q @0
}

func @forever(%a: i7) -> i7, i7, i7 {
^entry:
  %x: i7, %y: i7, %z: i7 = call @forever %a @0
  ret %z, %y, %x @0
}

locs {
  @0 = unknown
}
