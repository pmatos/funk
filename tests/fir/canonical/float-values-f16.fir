func @choose(%c: i1, %x: f16, %y: f16) -> f16 {
^entry:
  cond_br %c, ^left(%x), ^right(%y) @0
^left(%l: f16):
  br ^join(%l) @0
^right(%r: f16):
  br ^join(%r) @0
^join(%j: f16):
  ret %j @0
}

func @swap(%x: f16, %y: f16) -> f16, f16 {
^entry:
  ret %y, %x @0
}

func @calls(%c: i1, %x: f16, %y: f16) -> f16, f16, f16 {
^entry:
  %m: f16 = call @choose %c, %x, %y @0
  %a: f16, %b: f16 = call @swap %x, %y @0
  ret %m, %a, %b @0
}

locs {
  @0 = unknown
}
