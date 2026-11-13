func @f16_bf16(%a: f16) -> bf16 {
^entry:
  %r: bf16 = fptrunc round(rne) %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
