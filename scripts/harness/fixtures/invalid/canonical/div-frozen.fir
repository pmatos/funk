func @sdiv_frozen(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %b, %one @0
  %f: i8 = freeze %p @0
  %r: i8 = sdiv %a, %f @0
  ret %r @0
}

locs {
  @0 = unknown
}
