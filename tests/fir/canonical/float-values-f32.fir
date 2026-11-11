func @choose(%c: i1, %x: f32, %y: f32) -> f32 {
^entry:
  cond_br %c, ^left(%x), ^right(%y) @0
^left(%l: f32):
  br ^join(%l) @0
^right(%r: f32):
  br ^join(%r) @0
^join(%j: f32):
  ret %j @0
}

func @swap(%x: f32, %y: f32) -> f32, f32 {
^entry:
  ret %y, %x @0
}

func @calls(%c: i1, %x: f32, %y: f32) -> f32, f32, f32 {
^entry:
  %m: f32 = call @choose %c, %x, %y @0
  %a: f32, %b: f32 = call @swap %x, %y @0
  ret %m, %a, %b @0
}

locs {
  @0 = unknown
}
