func @f32_f128(%a: f32) -> f128 {
^entry:
  %r: f128 = fpext %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
