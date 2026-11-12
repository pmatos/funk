func @to_bits(%a: f32) -> i32 {
^entry:
  %r: i32 = bitcast %a @0
  ret %r @0
}

func @of_bits(%a: i32) -> f32 {
^entry:
  %r: f32 = bitcast %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
