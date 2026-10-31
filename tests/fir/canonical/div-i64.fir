func @sdiv(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = sdiv %a, %b @0
  ret %r @0
}

func @sdiv_exact(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = sdiv exact %a, %b @0
  ret %r @0
}

func @udiv(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = udiv %a, %b @0
  ret %r @0
}

func @udiv_exact(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = udiv exact %a, %b @0
  ret %r @0
}

func @srem(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = srem %a, %b @0
  ret %r @0
}

func @urem(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = urem %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
