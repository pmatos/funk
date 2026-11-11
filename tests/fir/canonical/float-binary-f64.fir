func @fadd(%a: f64, %b: f64) -> f64 {
^entry:
  %r: f64 = fadd round(rne) %a, %b @0
  ret %r @0
}

func @fsub(%a: f64, %b: f64) -> f64 {
^entry:
  %r: f64 = fsub round(rne) %a, %b @0
  ret %r @0
}

func @fmul(%a: f64, %b: f64) -> f64 {
^entry:
  %r: f64 = fmul round(rne) %a, %b @0
  ret %r @0
}

func @fdiv(%a: f64, %b: f64) -> f64 {
^entry:
  %r: f64 = fdiv round(rne) %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
