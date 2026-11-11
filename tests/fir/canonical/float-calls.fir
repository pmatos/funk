func @many(%x0: f64, %x1: i64, %x2: f32, %x3: f64, %x4: i64, %x5: f32, %x6: f64, %x7: i64, %x8: f32, %x9: f64, %x10: i64, %x11: f32, %x12: f64, %x13: i64, %x14: f32, %x15: f64, %x16: i64, %x17: f32) -> f32, f64, i64 {
^entry:
  ret %x17, %x15, %x16 @0
}

func @call_many(%x0: f64, %x1: i64, %x2: f32, %x3: f64, %x4: i64, %x5: f32, %x6: f64, %x7: i64, %x8: f32, %x9: f64, %x10: i64, %x11: f32, %x12: f64, %x13: i64, %x14: f32, %x15: f64, %x16: i64, %x17: f32) -> f64, f32, i64 {
^entry:
  %a: f32, %b: f64, %c: i64 = call @many %x0, %x1, %x2, %x3, %x4, %x5, %x6, %x7, %x8, %x9, %x10, %x11, %x12, %x13, %x14, %x15, %x16, %x17 @0
  ret %b, %a, %c @0
}

func @two(%x: f32, %y: f64) -> f64, f32 {
^entry:
  ret %y, %x @0
}

func @mixed(%i: i64, %x: f64) -> f64, i64 {
^entry:
  %y: f64, %j: i64 = call @flip %x, %i @0
  ret %y, %j @0
}

func @flip(%x: f64, %i: i64) -> f64, i64 {
^entry:
  ret %x, %i @0
}

func @wide(%w: i128, %x: f32) -> f32, i128 {
^entry:
  ret %x, %w @0
}

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

func @max(%x: f32, %y: f32) -> f32 {
^entry:
  %gt: i1 = fcmp ogt %x, %y @0
  cond_br %gt, ^done(%x), ^done(%y) @0
^done(%m: f32):
  ret %m @0
}

locs {
  @0 = unknown
}
