func @fneg(%a: f64) -> f64 {
^entry:
  %r: f64 = fneg %a @0
  ret %r @0
}

func @fabs(%a: f64) -> f64 {
^entry:
  %r: f64 = fabs %a @0
  ret %r @0
}

func @sqrt(%a: f64) -> f64 {
^entry:
  %r: f64 = sqrt round(rne) %a @0
  ret %r @0
}

func @fma(%a: f64, %b: f64, %c: f64) -> f64 {
^entry:
  %r: f64 = fma round(rne) %a, %b, %c @0
  ret %r @0
}

locs {
  @0 = unknown
}
