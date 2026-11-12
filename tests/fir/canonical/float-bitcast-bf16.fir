func @to_bits(%a: bf16) -> i16 {
^entry:
  %r: i16 = bitcast %a @0
  ret %r @0
}

func @of_bits(%a: i16) -> bf16 {
^entry:
  %r: bf16 = bitcast %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
