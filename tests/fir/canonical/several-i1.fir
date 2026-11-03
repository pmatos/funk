func @none(%a: i1) {
^entry:
  %b: i1 = add %a, %a @0
  ret @0
}

func @call_none(%a: i1) -> i1 {
^entry:
  call @none %a @0
  ret %a @0
}

func @two(%a: i1, %b: i1) -> i1, i1 {
^entry:
  %s: i1 = add %a, %b @0
  ret %s, %a @0
}

func @three(%a: i1, %b: i1) -> i1, i1, i1 {
^entry:
  %d: i1 = sub %a, %b @0
  %s: i1 = add %a, %b @0
  ret %d, %s, %b @0
}

func @eight(%a: i1) -> i1, i1, i1, i1, i1, i1, i1, i1 {
^entry:
  %one: i1 = const true @0
  %a1: i1 = add %a, %one @0
  %a2: i1 = add %a1, %one @0
  %a3: i1 = add %a2, %one @0
  %a4: i1 = add %a3, %one @0
  %a5: i1 = add %a4, %one @0
  %a6: i1 = add %a5, %one @0
  %a7: i1 = add %a6, %one @0
  ret %a, %a1, %a2, %a3, %a4, %a5, %a6, %a7 @0
}

func @use(%a: i1, %b: i1) -> i1, i1, i1 {
^entry:
  %d: i1, %s: i1, %c: i1 = call @three %a, %b @0
  %x: i1, %y: i1 = call @two %d, %s @0
  %e0: i1, %e1: i1, %e2: i1, %e3: i1, %e4: i1, %e5: i1, %e6: i1, %e7: i1 = call @eight %y @0
  ret %x, %e7, %c @0
}

func @fibs(%n: i1) -> i1, i1 {
^entry:
  %zero: i1 = const false @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^base, ^rec @0
^base:
  %one: i1 = const true @0
  ret %zero, %one @0
^rec:
  %one1: i1 = const true @0
  %m: i1 = sub %n, %one1 @0
  %a: i1, %b: i1 = call @fibs %m @0
  %s: i1 = add %a, %b @0
  ret %b, %s @0
}

func @trib(%n: i1) -> i1, i1, i1 {
^entry:
  %zero: i1 = const false @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^base, ^rec @0
^base:
  %one: i1 = const true @0
  ret %zero, %zero, %one @0
^rec:
  %one1: i1 = const true @0
  %m: i1 = sub %n, %one1 @0
  %a: i1, %b: i1, %c: i1 = call @trib %m @0
  %ab: i1 = add %a, %b @0
  %s: i1 = add %ab, %c @0
  ret %b, %c, %s @0
}

func @even(%n: i1) -> i1, i1, i1 {
^entry:
  %zero: i1 = const false @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const true @0
  ret %r, %zero, %zero @0
^more:
  %one: i1 = const true @0
  %m: i1 = sub %n, %one @0
  %p: i1, %k: i1, %d: i1 = call @odd %m @0
  %k1: i1 = add %k, %one @0
  %two: i1 = const false @0
  %d2: i1 = add %d, %two @0
  ret %p, %k1, %d2 @0
}

func @odd(%n: i1) -> i1, i1, i1 {
^entry:
  %zero: i1 = const false @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const false @0
  ret %r, %zero, %zero @0
^more:
  %one: i1 = const true @0
  %m: i1 = sub %n, %one @0
  %p: i1, %k: i1, %d: i1 = call @even %m @0
  %k1: i1 = add %k, %one @0
  %two: i1 = const false @0
  %d2: i1 = add %d, %two @0
  ret %p, %k1, %d2 @0
}

func @poison(%a: i1) -> i1, i1, i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  ret %a, %p, %one @0
}

func @call_poison(%a: i1) -> i1, i1, i1 {
^entry:
  %x: i1, %y: i1, %z: i1 = call @poison %a @0
  ret %z, %y, %x @0
}

func @divmod(%a: i1, %b: i1) -> i1, i1, i1 {
^entry:
  %q: i1 = udiv %a, %b @0
  %r: i1 = urem %a, %b @0
  ret %q, %r, %b @0
}

func @call_divmod(%a: i1, %b: i1) -> i1, i1 {
^entry:
  %q: i1, %r: i1, %c: i1 = call @divmod %a, %b @0
  ret %r, %q @0
}

func @forever(%a: i1) -> i1, i1, i1 {
^entry:
  %x: i1, %y: i1, %z: i1 = call @forever %a @0
  ret %z, %y, %x @0
}

locs {
  @0 = unknown
}
