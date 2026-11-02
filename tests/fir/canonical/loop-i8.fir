func @sum(%n: i8) -> i8 {
^entry:
  %zero: i8 = const 0 @0
  br ^loop(%zero, %zero) @0
^loop(%i: i8, %acc: i8):
  %done: i1 = icmp sge %i, %n @0
  cond_br %done, ^exit(%acc), ^body @0
^body:
  %acc1: i8 = add nsw %acc, %i @0
  %one: i8 = const 1 @0
  %i1: i8 = add nsw %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i8):
  ret %r @0
}

func @fact(%n: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  br ^loop(%n, %one) @0
^loop(%i: i8, %acc: i8):
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %i, %zero @0
  cond_br %done, ^exit(%acc), ^body @0
^body:
  %acc1: i8 = mul %acc, %i @0
  %i1: i8 = sub %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i8):
  ret %r @0
}

func @gcd(%a: i8, %b: i8) -> i8 {
^entry:
  br ^loop(%a, %b) @0
^loop(%x: i8, %y: i8):
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %y, %zero @0
  cond_br %done, ^exit(%x), ^body @0
^body:
  %r: i8 = urem %x, %y @0
  br ^loop(%y, %r) @0
^exit(%g: i8):
  ret %g @0
}

locs {
  @0 = unknown
}
