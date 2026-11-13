func @f64_f32(%a: f64) -> f32 {
^entry:
  %r: f32 = fptrunc round(rne) %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
