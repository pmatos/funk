func @fneg(%a: f128) -> f128 {
^entry:
  %r: f128 = fneg %a @0
  ret %r @0
}

func @fabs(%a: f128) -> f128 {
^entry:
  %r: f128 = fabs %a @0
  ret %r @0
}

func @sqrt(%a: f128) -> f128 {
^entry:
  %r: f128 = sqrt round(rne) %a @0
  ret %r @0
}

func @fma(%a: f128, %b: f128, %c: f128) -> f128 {
^entry:
  %r: f128 = fma round(rne) %a, %b, %c @0
  ret %r @0
}

locs {
  @0 = unknown
}
