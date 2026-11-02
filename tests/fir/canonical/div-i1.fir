func @sdiv(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = sdiv %a, %b @0
  ret %r @0
}

func @sdiv_exact(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = sdiv exact %a, %b @0
  ret %r @0
}

func @udiv(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = udiv %a, %b @0
  ret %r @0
}

func @udiv_exact(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = udiv exact %a, %b @0
  ret %r @0
}

func @srem(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = srem %a, %b @0
  ret %r @0
}

func @urem(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = urem %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
