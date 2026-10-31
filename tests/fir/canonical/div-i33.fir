func @sdiv(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = sdiv %a, %b @0
  ret %r @0
}

func @sdiv_exact(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = sdiv exact %a, %b @0
  ret %r @0
}

func @udiv(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = udiv %a, %b @0
  ret %r @0
}

func @udiv_exact(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = udiv exact %a, %b @0
  ret %r @0
}

func @srem(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = srem %a, %b @0
  ret %r @0
}

func @urem(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = urem %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
