func @choose(%c: i1, %x: f128, %y: f128) -> f128 {
^entry:
  cond_br %c, ^left(%x), ^right(%y) @0
^left(%l: f128):
  br ^join(%l) @0
^right(%r: f128):
  br ^join(%r) @0
^join(%j: f128):
  ret %j @0
}

func @swap(%x: f128, %y: f128) -> f128, f128 {
^entry:
  ret %y, %x @0
}

func @calls(%c: i1, %x: f128, %y: f128) -> f128, f128, f128 {
^entry:
  %m: f128 = call @choose %c, %x, %y @0
  %a: f128, %b: f128 = call @swap %x, %y @0
  ret %m, %a, %b @0
}

locs {
  @0 = unknown
}
