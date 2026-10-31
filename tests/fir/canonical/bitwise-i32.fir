func @and(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = and %a, %b @0
  ret %r @0
}

func @or(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = or %a, %b @0
  ret %r @0
}

func @xor(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = xor %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
