func @shl(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = shl %a, %b @0
  ret %r @0
}

func @lshr(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = lshr %a, %b @0
  ret %r @0
}

func @ashr(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = ashr %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
