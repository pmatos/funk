func @f128_f16(%a: f128) -> f16 {
^entry:
  %r: f16 = fptrunc round(rne) %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
