func @fact(%n: i128) -> i128 {
^entry:
  %zero: i128 = const 0 @0
  %more: i1 = icmp sgt %n, %zero @0
  cond_br %more, ^rec, ^base @0
^rec:
  %one: i128 = const 1 @0
  %m: i128 = sub %n, %one @0
  %f: i128 = call @fact %m @0
  %p: i128 = mul %n, %f @0
  ret %p @0
^base:
  %b: i128 = const 1 @0
  ret %b @0
}

func @fib(%n: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %small: i1 = icmp ule %n, %one @0
  cond_br %small, ^base, ^rec @0
^base:
  ret %n @0
^rec:
  %a: i128 = sub %n, %one @0
  %b: i128 = sub %a, %one @0
  %fa: i128 = call @fib %a @0
  %fb: i128 = call @fib %b @0
  %s: i128 = add %fa, %fb @0
  ret %s @0
}

func @scale(%n: i128, %k: i128) -> i128 {
^entry:
  %zero: i128 = const 0 @0
  %more: i1 = icmp sgt %n, %zero @0
  cond_br %more, ^rec, ^base @0
^rec:
  %one: i128 = const 1 @0
  %m: i128 = sub %n, %one @0
  %f: i128 = call @scale %m, %k @0
  %p: i128 = mul %f, %k @0
  ret %p @0
^base:
  ret %k @0
}

locs {
  @0 = unknown
}
