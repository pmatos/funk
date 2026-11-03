func @udiv(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = udiv %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
