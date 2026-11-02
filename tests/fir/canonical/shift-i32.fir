func @shl(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = shl %a, %b @0
  ret %r @0
}

func @lshr(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = lshr %a, %b @0
  ret %r @0
}

func @ashr(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = ashr %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
