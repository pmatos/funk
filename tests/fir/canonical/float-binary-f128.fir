func @fadd(%a: f128, %b: f128) -> f128 {
^entry:
  %r: f128 = fadd round(rne) %a, %b @0
  ret %r @0
}

func @fsub(%a: f128, %b: f128) -> f128 {
^entry:
  %r: f128 = fsub round(rne) %a, %b @0
  ret %r @0
}

func @fmul(%a: f128, %b: f128) -> f128 {
^entry:
  %r: f128 = fmul round(rne) %a, %b @0
  ret %r @0
}

func @fdiv(%a: f128, %b: f128) -> f128 {
^entry:
  %r: f128 = fdiv round(rne) %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
