func @fadd(%a: f32, %b: f32) -> f32 {
^entry:
  %r: f32 = fadd round(rne) %a, %b @0
  ret %r @0
}

func @fsub(%a: f32, %b: f32) -> f32 {
^entry:
  %r: f32 = fsub round(rne) %a, %b @0
  ret %r @0
}

func @fmul(%a: f32, %b: f32) -> f32 {
^entry:
  %r: f32 = fmul round(rne) %a, %b @0
  ret %r @0
}

func @fdiv(%a: f32, %b: f32) -> f32 {
^entry:
  %r: f32 = fdiv round(rne) %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
