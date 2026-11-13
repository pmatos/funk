func @bf16_f16(%a: bf16) -> f16 {
^entry:
  %r: f16 = fptrunc round(rne) %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
