func @f32_f64(%a: f32) -> f64 {
^entry:
  %r: f64 = fpext %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
