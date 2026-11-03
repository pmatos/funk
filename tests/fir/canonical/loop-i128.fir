func @sum(%n: i128, %step: i128) -> i128 {
^entry:
  %zero: i128 = const 0 @0
  br ^loop(%zero, %zero) @0
^loop(%i: i128, %acc: i128):
  %done: i1 = icmp sge %i, %n @0
  cond_br %done, ^exit(%acc), ^body @0
^body:
  %acc1: i128 = add nsw %acc, %step @0
  %one: i128 = const 1 @0
  %i1: i128 = add nsw %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i128):
  ret %r @0
}

func @fact(%n: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  br ^loop(%n, %one) @0
^loop(%i: i128, %acc: i128):
  %zero: i128 = const 0 @0
  %done: i1 = icmp eq %i, %zero @0
  cond_br %done, ^exit(%acc), ^body @0
^body:
  %acc1: i128 = mul %acc, %i @0
  %i1: i128 = sub %i, %one @0
  br ^loop(%i1, %acc1) @0
^exit(%r: i128):
  ret %r @0
}

locs {
  @0 = unknown
}
