func @sdiv(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = sdiv %a, %b @0
  ret %r @0
}

func @sdiv_exact(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = sdiv exact %a, %b @0
  ret %r @0
}

func @udiv(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = udiv %a, %b @0
  ret %r @0
}

func @udiv_exact(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = udiv exact %a, %b @0
  ret %r @0
}

func @srem(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = srem %a, %b @0
  ret %r @0
}

func @urem(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = urem %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
