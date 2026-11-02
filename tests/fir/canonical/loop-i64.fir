func @sum(%n: i64) -> i64 {
^entry:
  %zero: i64 = const 0 @0
  br ^loop(%zero, %zero) @0
^loop(%i: i64, %acc: i64):
  %done: i1 = icmp sge %i, %n @0
  cond_br %done, ^exit(%acc), ^body @0
^body:
  %acc1: i64 = add nsw %acc, %i @0
  %one: i64 = const 1 @0
  %i1: i64 = add nsw %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i64):
  ret %r @0
}

func @fact(%n: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  br ^loop(%n, %one) @0
^loop(%i: i64, %acc: i64):
  %zero: i64 = const 0 @0
  %done: i1 = icmp eq %i, %zero @0
  cond_br %done, ^exit(%acc), ^body @0
^body:
  %acc1: i64 = mul %acc, %i @0
  %i1: i64 = sub %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i64):
  ret %r @0
}

func @gcd(%a: i64, %b: i64) -> i64 {
^entry:
  br ^loop(%a, %b) @0
^loop(%x: i64, %y: i64):
  %zero: i64 = const 0 @0
  %done: i1 = icmp eq %y, %zero @0
  cond_br %done, ^exit(%x), ^body @0
^body:
  %r: i64 = urem %x, %y @0
  br ^loop(%y, %r) @0
^exit(%g: i64):
  ret %g @0
}

locs {
  @0 = unknown
}
