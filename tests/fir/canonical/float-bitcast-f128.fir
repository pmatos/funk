func @to_bits(%a: f128) -> i128 {
^entry:
  %r: i128 = bitcast %a @0
  ret %r @0
}

func @of_bits(%a: i128) -> f128 {
^entry:
  %r: f128 = bitcast %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
