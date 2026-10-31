func @shl(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = shl %a, %b @0
  ret %r @0
}

func @lshr(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = lshr %a, %b @0
  ret %r @0
}

func @ashr(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = ashr %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
