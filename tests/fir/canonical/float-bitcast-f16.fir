func @to_bits(%a: f16) -> i16 {
^entry:
  %r: i16 = bitcast %a @0
  ret %r @0
}

func @of_bits(%a: i16) -> f16 {
^entry:
  %r: f16 = bitcast %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
