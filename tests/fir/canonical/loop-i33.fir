func @sum(%n: i33) -> i33 {
^entry:
  %zero: i33 = const 0 @0
  br ^loop(%zero, %zero) @0
^loop(%i: i33, %acc: i33):
  %done: i1 = icmp sge %i, %n @0
  cond_br %done, ^exit(%acc), ^body @0
^body:
  %acc1: i33 = add nsw %acc, %i @0
  %one: i33 = const 1 @0
  %i1: i33 = add nsw %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i33):
  ret %r @0
}

func @fact(%n: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  br ^loop(%n, %one) @0
^loop(%i: i33, %acc: i33):
  %zero: i33 = const 0 @0
  %done: i1 = icmp eq %i, %zero @0
  cond_br %done, ^exit(%acc), ^body @0
^body:
  %acc1: i33 = mul %acc, %i @0
  %i1: i33 = sub %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i33):
  ret %r @0
}

func @gcd(%a: i33, %b: i33) -> i33 {
^entry:
  br ^loop(%a, %b) @0
^loop(%x: i33, %y: i33):
  %zero: i33 = const 0 @0
  %done: i1 = icmp eq %y, %zero @0
  cond_br %done, ^exit(%x), ^body @0
^body:
  %r: i33 = urem %x, %y @0
  br ^loop(%y, %r) @0
^exit(%g: i33):
  ret %g @0
}

locs {
  @0 = unknown
}
