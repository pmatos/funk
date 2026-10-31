func @sum(%n: i32) -> i32 {
^entry:
  %zero: i32 = const 0 @0
  br ^loop(%zero, %zero) @0
^loop(%i: i32, %acc: i32):
  %done: i1 = icmp sge %i, %n @0
  cond_br %done, ^exit(%acc), ^body @0
^body:
  %acc1: i32 = add nsw %acc, %i @0
  %one: i32 = const 1 @0
  %i1: i32 = add nsw %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i32):
  ret %r @0
}

func @fact(%n: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  br ^loop(%n, %one) @0
^loop(%i: i32, %acc: i32):
  %zero: i32 = const 0 @0
  %done: i1 = icmp eq %i, %zero @0
  cond_br %done, ^exit(%acc), ^body @0
^body:
  %acc1: i32 = mul %acc, %i @0
  %i1: i32 = sub %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i32):
  ret %r @0
}

func @gcd(%a: i32, %b: i32) -> i32 {
^entry:
  br ^loop(%a, %b) @0
^loop(%x: i32, %y: i32):
  %zero: i32 = const 0 @0
  %done: i1 = icmp eq %y, %zero @0
  cond_br %done, ^exit(%x), ^body @0
^body:
  %r: i32 = urem %x, %y @0
  br ^loop(%y, %r) @0
^exit(%g: i32):
  ret %g @0
}

locs {
  @0 = unknown
}
