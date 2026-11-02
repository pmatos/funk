func @shl(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = shl %a, %b @0
  ret %r @0
}

func @lshr(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = lshr %a, %b @0
  ret %r @0
}

func @ashr(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = ashr %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
