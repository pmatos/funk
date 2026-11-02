func @freeze_xor(%a: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %f: i64 = freeze %p @0
  %d: i64 = xor %f, %f @0
  ret %d @0
}

locs {
  @0 = unknown
}
