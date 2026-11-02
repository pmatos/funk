func @and(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = and %a, %b @0
  ret %r @0
}

func @or(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = or %a, %b @0
  ret %r @0
}

func @xor(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = xor %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
