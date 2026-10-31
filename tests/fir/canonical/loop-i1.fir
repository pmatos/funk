func @sum(%n: i1) -> i1 {
^entry:
  %zero: i1 = const false @0
  br ^loop(%zero, %zero) @0
^loop(%i: i1, %acc: i1):
  %done: i1 = icmp sge %i, %n @0
  cond_br %done, ^exit(%acc), ^body @0
^body:
  %acc1: i1 = add nsw %acc, %i @0
  %one: i1 = const true @0
  %i1: i1 = add nsw %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i1):
  ret %r @0
}

func @fact(%n: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  br ^loop(%n, %one) @0
^loop(%i: i1, %acc: i1):
  %zero: i1 = const false @0
  %done: i1 = icmp eq %i, %zero @0
  cond_br %done, ^exit(%acc), ^body @0
^body:
  %acc1: i1 = mul %acc, %i @0
  %i1: i1 = sub %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i1):
  ret %r @0
}

func @gcd(%a: i1, %b: i1) -> i1 {
^entry:
  br ^loop(%a, %b) @0
^loop(%x: i1, %y: i1):
  %zero: i1 = const false @0
  %done: i1 = icmp eq %y, %zero @0
  cond_br %done, ^exit(%x), ^body @0
^body:
  %r: i1 = urem %x, %y @0
  br ^loop(%y, %r) @0
^exit(%g: i1):
  ret %g @0
}

locs {
  @0 = unknown
}
