func @to_bits(%a: f64) -> i64 {
^entry:
  %r: i64 = bitcast %a @0
  ret %r @0
}

func @of_bits(%a: i64) -> f64 {
^entry:
  %r: f64 = bitcast %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
