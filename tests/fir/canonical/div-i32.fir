func @sdiv(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = sdiv %a, %b @0
  ret %r @0
}

func @sdiv_exact(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = sdiv exact %a, %b @0
  ret %r @0
}

func @udiv(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = udiv %a, %b @0
  ret %r @0
}

func @udiv_exact(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = udiv exact %a, %b @0
  ret %r @0
}

func @srem(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = srem %a, %b @0
  ret %r @0
}

func @urem(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = urem %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
