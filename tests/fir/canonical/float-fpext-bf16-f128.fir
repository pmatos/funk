func @bf16_f128(%a: bf16) -> f128 {
^entry:
  %r: f128 = fpext %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
