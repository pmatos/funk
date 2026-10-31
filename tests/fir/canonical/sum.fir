func @sum(%n: i32) -> i32 {
^entry:
  %zero: i32 = const 0 @1
  br ^loop(%zero, %zero) @1
^loop(%i: i32, %acc: i32):
  %done: i1 = icmp sge %i, %n @2
  cond_br %done, ^exit(%acc), ^body @2
^body:
  %acc1: i32 = add nsw %acc, %i @3
  %one: i32 = const 1 @3
  %i1: i32 = add nsw %i, %one @3
  br ^loop(%i1, %acc1) @3
^exit(%r: i32):
  ret %r @4
}

locs {
  @0 = unknown
  @1 = "sum.c":2:3 to 2:15
  @2 = "sum.c":3:10 to 3:16
  @3 = "sum.c":4:5 to 4:17
  @4 = "sum.c":6:3 to 6:14
}
