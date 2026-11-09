func @down(%n: i64) -> i64 {
^entry:
  %zero: i64 = const 0 @0
  %more: i1 = icmp sgt %n, %zero @0
  cond_br %more, ^rec, ^base @0
^rec:
  %one: i64 = const 1 @0
  %m: i64 = sub %n, %one @0
  %d: i64 = call @down %m @0
  %s: i64 = add %d, %one @0
  ret %s @0
^base:
  ret %n @0
}

locs {
  @0 = unknown
}
