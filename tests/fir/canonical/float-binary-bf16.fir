func @fadd(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fadd round(rne) %a, %b @0
  ret %r @0
}

func @fsub(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fsub round(rne) %a, %b @0
  ret %r @0
}

func @fmul(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fmul round(rne) %a, %b @0
  ret %r @0
}

func @fdiv(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fdiv round(rne) %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
