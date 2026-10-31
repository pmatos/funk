func @sdiv(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = sdiv %a, %b @0
  ret %r @0
}

func @sdiv_exact(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = sdiv exact %a, %b @0
  ret %r @0
}

func @udiv(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = udiv %a, %b @0
  ret %r @0
}

func @udiv_exact(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = udiv exact %a, %b @0
  ret %r @0
}

func @srem(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = srem %a, %b @0
  ret %r @0
}

func @urem(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = urem %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
