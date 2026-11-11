func @fadd(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fadd round(rne) %a, %b @0
  ret %r @0
}

func @fsub(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fsub round(rne) %a, %b @0
  ret %r @0
}

func @fmul(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fmul round(rne) %a, %b @0
  ret %r @0
}

func @fdiv(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fdiv round(rne) %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
