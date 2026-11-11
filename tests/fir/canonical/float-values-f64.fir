func @choose(%c: i1, %x: f64, %y: f64) -> f64 {
^entry:
  cond_br %c, ^left(%x), ^right(%y) @0
^left(%l: f64):
  br ^join(%l) @0
^right(%r: f64):
  br ^join(%r) @0
^join(%j: f64):
  ret %j @0
}

func @swap(%x: f64, %y: f64) -> f64, f64 {
^entry:
  ret %y, %x @0
}

func @calls(%c: i1, %x: f64, %y: f64) -> f64, f64, f64 {
^entry:
  %m: f64 = call @choose %c, %x, %y @0
  %a: f64, %b: f64 = call @swap %x, %y @0
  ret %m, %a, %b @0
}

locs {
  @0 = unknown
}
