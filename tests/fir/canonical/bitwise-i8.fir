func @and(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = and %a, %b @0
  ret %r @0
}

func @or(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = or %a, %b @0
  ret %r @0
}

func @xor(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = xor %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
