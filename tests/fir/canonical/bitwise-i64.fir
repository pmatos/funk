func @and(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = and %a, %b @0
  ret %r @0
}

func @or(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = or %a, %b @0
  ret %r @0
}

func @xor(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = xor %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
