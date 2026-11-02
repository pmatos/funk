func @sdiv(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = sdiv %a, %b @0
  ret %r @0
}

func @sdiv_exact(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = sdiv exact %a, %b @0
  ret %r @0
}

func @udiv(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = udiv %a, %b @0
  ret %r @0
}

func @udiv_exact(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = udiv exact %a, %b @0
  ret %r @0
}

func @srem(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = srem %a, %b @0
  ret %r @0
}

func @urem(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = urem %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
