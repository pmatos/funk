func @and(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = and %a, %b @0
  ret %r @0
}

func @or(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = or %a, %b @0
  ret %r @0
}

func @xor(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = xor %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
