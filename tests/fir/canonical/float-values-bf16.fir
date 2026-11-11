func @choose(%c: i1, %x: bf16, %y: bf16) -> bf16 {
^entry:
  cond_br %c, ^left(%x), ^right(%y) @0
^left(%l: bf16):
  br ^join(%l) @0
^right(%r: bf16):
  br ^join(%r) @0
^join(%j: bf16):
  ret %j @0
}

func @swap(%x: bf16, %y: bf16) -> bf16, bf16 {
^entry:
  ret %y, %x @0
}

func @calls(%c: i1, %x: bf16, %y: bf16) -> bf16, bf16, bf16 {
^entry:
  %m: bf16 = call @choose %c, %x, %y @0
  %a: bf16, %b: bf16 = call @swap %x, %y @0
  ret %m, %a, %b @0
}

locs {
  @0 = unknown
}
