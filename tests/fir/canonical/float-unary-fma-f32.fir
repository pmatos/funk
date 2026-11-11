func @fneg(%a: f32) -> f32 {
^entry:
  %r: f32 = fneg %a @0
  ret %r @0
}

func @fabs(%a: f32) -> f32 {
^entry:
  %r: f32 = fabs %a @0
  ret %r @0
}

func @sqrt(%a: f32) -> f32 {
^entry:
  %r: f32 = sqrt round(rne) %a @0
  ret %r @0
}

func @fma(%a: f32, %b: f32, %c: f32) -> f32 {
^entry:
  %r: f32 = fma round(rne) %a, %b, %c @0
  ret %r @0
}

locs {
  @0 = unknown
}
