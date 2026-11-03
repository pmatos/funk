func @none(%a: i33) {
^entry:
  %b: i33 = add %a, %a @0
  ret @0
}

func @call_none(%a: i33) -> i33 {
^entry:
  call @none %a @0
  ret %a @0
}

func @two(%a: i33, %b: i33) -> i33, i33 {
^entry:
  %s: i33 = add %a, %b @0
  ret %s, %a @0
}

func @three(%a: i33, %b: i33) -> i33, i33, i33 {
^entry:
  %d: i33 = sub %a, %b @0
  %s: i33 = add %a, %b @0
  ret %d, %s, %b @0
}

func @eight(%a: i33) -> i33, i33, i33, i33, i33, i33, i33, i33 {
^entry:
  %one: i33 = const 1 @0
  %a1: i33 = add %a, %one @0
  %a2: i33 = add %a1, %one @0
  %a3: i33 = add %a2, %one @0
  %a4: i33 = add %a3, %one @0
  %a5: i33 = add %a4, %one @0
  %a6: i33 = add %a5, %one @0
  %a7: i33 = add %a6, %one @0
  ret %a, %a1, %a2, %a3, %a4, %a5, %a6, %a7 @0
}

func @use(%a: i33, %b: i33) -> i33, i33, i33 {
^entry:
  %d: i33, %s: i33, %c: i33 = call @three %a, %b @0
  %x: i33, %y: i33 = call @two %d, %s @0
  %e0: i33, %e1: i33, %e2: i33, %e3: i33, %e4: i33, %e5: i33, %e6: i33, %e7: i33 = call @eight %y @0
  ret %x, %e7, %c @0
}

func @fibs(%n: i33) -> i33, i33 {
^entry:
  %zero: i33 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^base, ^rec @0
^base:
  %one: i33 = const 1 @0
  ret %zero, %one @0
^rec:
  %one1: i33 = const 1 @0
  %m: i33 = sub %n, %one1 @0
  %a: i33, %b: i33 = call @fibs %m @0
  %s: i33 = add %a, %b @0
  ret %b, %s @0
}

func @trib(%n: i33) -> i33, i33, i33 {
^entry:
  %zero: i33 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^base, ^rec @0
^base:
  %one: i33 = const 1 @0
  ret %zero, %zero, %one @0
^rec:
  %one1: i33 = const 1 @0
  %m: i33 = sub %n, %one1 @0
  %a: i33, %b: i33, %c: i33 = call @trib %m @0
  %ab: i33 = add %a, %b @0
  %s: i33 = add %ab, %c @0
  ret %b, %c, %s @0
}

func @even(%n: i33) -> i1, i33, i33 {
^entry:
  %zero: i33 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const true @0
  ret %r, %zero, %zero @0
^more:
  %one: i33 = const 1 @0
  %m: i33 = sub %n, %one @0
  %p: i1, %k: i33, %d: i33 = call @odd %m @0
  %k1: i33 = add %k, %one @0
  %two: i33 = const 2 @0
  %d2: i33 = add %d, %two @0
  ret %p, %k1, %d2 @0
}

func @odd(%n: i33) -> i1, i33, i33 {
^entry:
  %zero: i33 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const false @0
  ret %r, %zero, %zero @0
^more:
  %one: i33 = const 1 @0
  %m: i33 = sub %n, %one @0
  %p: i1, %k: i33, %d: i33 = call @even %m @0
  %k1: i33 = add %k, %one @0
  %two: i33 = const 2 @0
  %d2: i33 = add %d, %two @0
  ret %p, %k1, %d2 @0
}

func @poison(%a: i33) -> i33, i33, i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  ret %a, %p, %one @0
}

func @call_poison(%a: i33) -> i33, i33, i33 {
^entry:
  %x: i33, %y: i33, %z: i33 = call @poison %a @0
  ret %z, %y, %x @0
}

func @divmod(%a: i33, %b: i33) -> i33, i33, i33 {
^entry:
  %q: i33 = udiv %a, %b @0
  %r: i33 = urem %a, %b @0
  ret %q, %r, %b @0
}

func @call_divmod(%a: i33, %b: i33) -> i33, i33 {
^entry:
  %q: i33, %r: i33, %c: i33 = call @divmod %a, %b @0
  ret %r, %q @0
}

func @forever(%a: i33) -> i33, i33, i33 {
^entry:
  %x: i33, %y: i33, %z: i33 = call @forever %a @0
  ret %z, %y, %x @0
}

locs {
  @0 = unknown
}
