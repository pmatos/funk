func @shl(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = shl %a, %b @0
  ret %r @0
}

func @lshr(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = lshr %a, %b @0
  ret %r @0
}

func @ashr(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = ashr %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
