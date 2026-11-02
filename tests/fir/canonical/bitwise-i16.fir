func @and(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = and %a, %b @0
  ret %r @0
}

func @or(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = or %a, %b @0
  ret %r @0
}

func @xor(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = xor %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
