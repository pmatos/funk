func @and(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = and %a, %b @0
  ret %r @0
}

func @or(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = or %a, %b @0
  ret %r @0
}

func @xor(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = xor %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
