func @aliases(%h: f16, %b: bf16, %s: f32, %d: f64, %q: f128) -> f128, f64, f32, bf16, f16 {
^entry:
  ret %q, %d, %s, %b, %h @0
}

func @generic(%a: float(2, 1), %b: float(4, 3), %c: float(5, 2), %d: float(8, 24)) -> float(8, 24), float(5, 2), float(4, 3), float(2, 1) {
^entry:
  ret %d, %c, %b, %a @0
}

func @widest(%x: float(2, 16777212)) -> float(2, 16777212) {
^entry:
  ret %x @0
}

func @pass(%c: i1, %x: f32, %y: f32) -> f32 {
^entry:
  cond_br %c, ^left(%x), ^right(%y) @0
^left(%l: f32):
  br ^join(%l) @0
^right(%r: f32):
  br ^join(%r) @0
^join(%j: f32):
  ret %j @0
}

func @swap(%x: f64, %y: bf16) -> bf16, f64 {
^entry:
  %a: bf16, %b: f64 = call @flip %x, %y @0
  ret %a, %b @0
}

func @flip(%x: f64, %y: bf16) -> bf16, f64 {
^entry:
  ret %y, %x @0
}

locs {
  @0 = unknown
}
