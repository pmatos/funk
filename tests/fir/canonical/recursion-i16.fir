func @fact(%n: i16) -> i16 {
^entry:
  %zero: i16 = const 0 @0
  %more: i1 = icmp sgt %n, %zero @0
  cond_br %more, ^rec, ^base @0
^rec:
  %one: i16 = const 1 @0
  %m: i16 = sub %n, %one @0
  %f: i16 = call @fact %m @0
  %p: i16 = mul %n, %f @0
  ret %p @0
^base:
  %b: i16 = const 1 @0
  ret %b @0
}

func @fib(%n: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %small: i1 = icmp ule %n, %one @0
  cond_br %small, ^base, ^rec @0
^base:
  ret %n @0
^rec:
  %a: i16 = sub %n, %one @0
  %b: i16 = sub %a, %one @0
  %fa: i16 = call @fib %a @0
  %fb: i16 = call @fib %b @0
  %s: i16 = add %fa, %fb @0
  ret %s @0
}

func @even(%n: i16) -> i1 {
^entry:
  %zero: i16 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const true @0
  ret %r @0
^more:
  %one: i16 = const 1 @0
  %m: i16 = sub %n, %one @0
  %o: i1 = call @odd %m @0
  ret %o @0
}

func @odd(%n: i16) -> i1 {
^entry:
  %zero: i16 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^stop, ^more @0
^stop:
  %r: i1 = const false @0
  ret %r @0
^more:
  %one: i16 = const 1 @0
  %m: i16 = sub %n, %one @0
  %o: i1 = call @even %m @0
  ret %o @0
}

locs {
  @0 = unknown
}
