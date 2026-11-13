func @bf16_f32(%a: bf16) -> f32 {
^entry:
  %r: f32 = fpext %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
