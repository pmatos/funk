func @f128_f64(%a: f128) -> f64 {
^entry:
  %r: f64 = fptrunc round(rne) %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
