func @fneg(%a: bf16) -> bf16 {
^entry:
  %r: bf16 = fneg %a @0
  ret %r @0
}

func @fabs(%a: bf16) -> bf16 {
^entry:
  %r: bf16 = fabs %a @0
  ret %r @0
}

func @sqrt(%a: bf16) -> bf16 {
^entry:
  %r: bf16 = sqrt round(rne) %a @0
  ret %r @0
}

func @fma(%a: bf16, %b: bf16, %c: bf16) -> bf16 {
^entry:
  %r: bf16 = fma round(rne) %a, %b, %c @0
  ret %r @0
}

locs {
  @0 = unknown
}
