func @shl(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = shl %a, %b @0
  ret %r @0
}

func @lshr(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = lshr %a, %b @0
  ret %r @0
}

func @ashr(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = ashr %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
