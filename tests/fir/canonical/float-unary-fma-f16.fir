func @fneg(%a: f16) -> f16 {
^entry:
  %r: f16 = fneg %a @0
  ret %r @0
}

func @fabs(%a: f16) -> f16 {
^entry:
  %r: f16 = fabs %a @0
  ret %r @0
}

func @sqrt(%a: f16) -> f16 {
^entry:
  %r: f16 = sqrt round(rne) %a @0
  ret %r @0
}

func @fma(%a: f16, %b: f16, %c: f16) -> f16 {
^entry:
  %r: f16 = fma round(rne) %a, %b, %c @0
  ret %r @0
}

locs {
  @0 = unknown
}
