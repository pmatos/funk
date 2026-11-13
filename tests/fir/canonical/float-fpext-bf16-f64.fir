func @bf16_f64(%a: bf16) -> f64 {
^entry:
  %r: f64 = fpext %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
