func @f16_f128(%a: f16) -> f128 {
^entry:
  %r: f128 = fpext %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
