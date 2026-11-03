func @freeze_xor(%a: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %f: i128 = freeze %p @0
  %d: i128 = xor %f, %f @0
  ret %d @0
}

locs {
  @0 = unknown
}
