func @and(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = and %a, %b @0
  ret %r @0
}

func @or(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = or %a, %b @0
  ret %r @0
}

func @xor(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = xor %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
