func @none(%a: i8) {
^entry:
  %b: i8 = add %a, %a @0
  ret @0
}

func @call_none(%a: i8) -> i8 {
^entry:
  call @none %a @0
  ret %a @0
}

func @two(%a: i8, %b: i8) -> i8, i8 {
^entry:
  %s: i8 = add %a, %b @0
  ret %s, %a @0
}

func @three(%a: i8, %b: i8) -> i8, i8, i8 {
^entry:
  %d: i8 = sub %a, %b @0
  %s: i8 = add %a, %b @0
  ret %d, %s, %b @0
}

func @eight(%a: i8) -> i8, i8, i8, i8, i8, i8, i8, i8 {
^entry:
  %one: i8 = const 1 @0
  %a1: i8 = add %a, %one @0
  %a2: i8 = add %a1, %one @0
  %a3: i8 = add %a2, %one @0
  %a4: i8 = add %a3, %one @0
  %a5: i8 = add %a4, %one @0
  %a6: i8 = add %a5, %one @0
  %a7: i8 = add %a6, %one @0
  ret %a, %a1, %a2, %a3, %a4, %a5, %a6, %a7 @0
}

func @use(%a: i8, %b: i8) -> i8, i8, i8 {
^entry:
  %d: i8, %s: i8, %c: i8 = call @three %a, %b @0
  %x: i8, %y: i8 = call @two %d, %s @0
  %e0: i8, %e1: i8, %e2: i8, %e3: i8, %e4: i8, %e5: i8, %e6: i8, %e7: i8 = call @eight %y @0
  ret %x, %e7, %c @0
}

func @fibs(%n: i8) -> i8, i8 {
^entry:
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^base, ^rec @0
^base:
  %one: i8 = const 1 @0
  ret %zero, %one @0
^rec:
  %one1: i8 = const 1 @0
  %m: i8 = sub %n, %one1 @0
  %a: i8, %b: i8 = call @fibs %m @0
  %s: i8 = add %a, %b @0
  ret %b, %s @0
}

func @trib(%n: i8) -> i8, i8, i8 {
^entry:
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^base, ^rec @0
^base:
  %one: i8 = const 1 @0
  ret %zero, %zero, %one @0
^rec:
  %one1: i8 = const 1 @0
  %m: i8 = sub %n, %one1 @0
  %a: i8, %b: i8, %c: i8 = call @trib %m @0
  %ab: i8 = add %a, %b @0
  %s: i8 = add %ab, %c @0
  ret %b, %c, %s @0
}

func @even(%n: i8) -> i1, i8, i8 {
^entry:
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const true @0
  ret %r, %zero, %zero @0
^more:
  %one: i8 = const 1 @0
  %m: i8 = sub %n, %one @0
  %p: i1, %k: i8, %d: i8 = call @odd %m @0
  %k1: i8 = add %k, %one @0
  %two: i8 = const 2 @0
  %d2: i8 = add %d, %two @0
  ret %p, %k1, %d2 @0
}

func @odd(%n: i8) -> i1, i8, i8 {
^entry:
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const false @0
  ret %r, %zero, %zero @0
^more:
  %one: i8 = const 1 @0
  %m: i8 = sub %n, %one @0
  %p: i1, %k: i8, %d: i8 = call @even %m @0
  %k1: i8 = add %k, %one @0
  %two: i8 = const 2 @0
  %d2: i8 = add %d, %two @0
  ret %p, %k1, %d2 @0
}

func @poison(%a: i8) -> i8, i8, i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  ret %a, %p, %one @0
}

func @call_poison(%a: i8) -> i8, i8, i8 {
^entry:
  %x: i8, %y: i8, %z: i8 = call @poison %a @0
  ret %z, %y, %x @0
}

func @divmod(%a: i8, %b: i8) -> i8, i8, i8 {
^entry:
  %q: i8 = udiv %a, %b @0
  %r: i8 = urem %a, %b @0
  ret %q, %r, %b @0
}

func @call_divmod(%a: i8, %b: i8) -> i8, i8 {
^entry:
  %q: i8, %r: i8, %c: i8 = call @divmod %a, %b @0
  ret %r, %q @0
}

func @forever(%a: i8) -> i8, i8, i8 {
^entry:
  %x: i8, %y: i8, %z: i8 = call @forever %a @0
  ret %z, %y, %x @0
}

locs {
  @0 = unknown
}
