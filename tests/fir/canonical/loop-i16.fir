func @sum(%n: i16) -> i16 {
^entry:
  %zero: i16 = const 0 @0
  br ^loop(%zero, %zero) @0
^loop(%i: i16, %acc: i16):
  %done: i1 = icmp sge %i, %n @0
  cond_br %done, ^exit(%acc), ^body @0
^body:
  %acc1: i16 = add nsw %acc, %i @0
  %one: i16 = const 1 @0
  %i1: i16 = add nsw %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i16):
  ret %r @0
}

func @fact(%n: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  br ^loop(%n, %one) @0
^loop(%i: i16, %acc: i16):
  %zero: i16 = const 0 @0
  %done: i1 = icmp eq %i, %zero @0
  cond_br %done, ^exit(%acc), ^body @0
^body:
  %acc1: i16 = mul %acc, %i @0
  %i1: i16 = sub %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i16):
  ret %r @0
}

func @gcd(%a: i16, %b: i16) -> i16 {
^entry:
  br ^loop(%a, %b) @0
^loop(%x: i16, %y: i16):
  %zero: i16 = const 0 @0
  %done: i1 = icmp eq %y, %zero @0
  cond_br %done, ^exit(%x), ^body @0
^body:
  %r: i16 = urem %x, %y @0
  br ^loop(%y, %r) @0
^exit(%g: i16):
  ret %g @0
}

locs {
  @0 = unknown
}
