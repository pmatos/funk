func @shl(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = shl %a, %b @0
  ret %r @0
}

func @lshr(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = lshr %a, %b @0
  ret %r @0
}

func @ashr(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = ashr %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
