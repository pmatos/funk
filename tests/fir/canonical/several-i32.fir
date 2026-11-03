func @none(%a: i32) {
^entry:
  %b: i32 = add %a, %a @0
  ret @0
}

func @call_none(%a: i32) -> i32 {
^entry:
  call @none %a @0
  ret %a @0
}

func @two(%a: i32, %b: i32) -> i32, i32 {
^entry:
  %s: i32 = add %a, %b @0
  ret %s, %a @0
}

func @three(%a: i32, %b: i32) -> i32, i32, i32 {
^entry:
  %d: i32 = sub %a, %b @0
  %s: i32 = add %a, %b @0
  ret %d, %s, %b @0
}

func @eight(%a: i32) -> i32, i32, i32, i32, i32, i32, i32, i32 {
^entry:
  %one: i32 = const 1 @0
  %a1: i32 = add %a, %one @0
  %a2: i32 = add %a1, %one @0
  %a3: i32 = add %a2, %one @0
  %a4: i32 = add %a3, %one @0
  %a5: i32 = add %a4, %one @0
  %a6: i32 = add %a5, %one @0
  %a7: i32 = add %a6, %one @0
  ret %a, %a1, %a2, %a3, %a4, %a5, %a6, %a7 @0
}

func @use(%a: i32, %b: i32) -> i32, i32, i32 {
^entry:
  %d: i32, %s: i32, %c: i32 = call @three %a, %b @0
  %x: i32, %y: i32 = call @two %d, %s @0
  %e0: i32, %e1: i32, %e2: i32, %e3: i32, %e4: i32, %e5: i32, %e6: i32, %e7: i32 = call @eight %y @0
  ret %x, %e7, %c @0
}

func @fibs(%n: i32) -> i32, i32 {
^entry:
  %zero: i32 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^base, ^rec @0
^base:
  %one: i32 = const 1 @0
  ret %zero, %one @0
^rec:
  %one1: i32 = const 1 @0
  %m: i32 = sub %n, %one1 @0
  %a: i32, %b: i32 = call @fibs %m @0
  %s: i32 = add %a, %b @0
  ret %b, %s @0
}

func @trib(%n: i32) -> i32, i32, i32 {
^entry:
  %zero: i32 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^base, ^rec @0
^base:
  %one: i32 = const 1 @0
  ret %zero, %zero, %one @0
^rec:
  %one1: i32 = const 1 @0
  %m: i32 = sub %n, %one1 @0
  %a: i32, %b: i32, %c: i32 = call @trib %m @0
  %ab: i32 = add %a, %b @0
  %s: i32 = add %ab, %c @0
  ret %b, %c, %s @0
}

func @even(%n: i32) -> i1, i32, i32 {
^entry:
  %zero: i32 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const true @0
  ret %r, %zero, %zero @0
^more:
  %one: i32 = const 1 @0
  %m: i32 = sub %n, %one @0
  %p: i1, %k: i32, %d: i32 = call @odd %m @0
  %k1: i32 = add %k, %one @0
  %two: i32 = const 2 @0
  %d2: i32 = add %d, %two @0
  ret %p, %k1, %d2 @0
}

func @odd(%n: i32) -> i1, i32, i32 {
^entry:
  %zero: i32 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const false @0
  ret %r, %zero, %zero @0
^more:
  %one: i32 = const 1 @0
  %m: i32 = sub %n, %one @0
  %p: i1, %k: i32, %d: i32 = call @even %m @0
  %k1: i32 = add %k, %one @0
  %two: i32 = const 2 @0
  %d2: i32 = add %d, %two @0
  ret %p, %k1, %d2 @0
}

func @poison(%a: i32) -> i32, i32, i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  ret %a, %p, %one @0
}

func @call_poison(%a: i32) -> i32, i32, i32 {
^entry:
  %x: i32, %y: i32, %z: i32 = call @poison %a @0
  ret %z, %y, %x @0
}

func @divmod(%a: i32, %b: i32) -> i32, i32, i32 {
^entry:
  %q: i32 = udiv %a, %b @0
  %r: i32 = urem %a, %b @0
  ret %q, %r, %b @0
}

func @call_divmod(%a: i32, %b: i32) -> i32, i32 {
^entry:
  %q: i32, %r: i32, %c: i32 = call @divmod %a, %b @0
  ret %r, %q @0
}

func @forever(%a: i32) -> i32, i32, i32 {
^entry:
  %x: i32, %y: i32, %z: i32 = call @forever %a @0
  ret %z, %y, %x @0
}

locs {
  @0 = unknown
}
