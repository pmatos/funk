func @consts() -> f32, f32, f32, f32, f32, f32, f32, f32, f32 {
^entry:
  %c0: f32 = const 0 @0
  %c1: f32 = const -2147483648 @0
  %c2: f32 = const 1 @0
  %c3: f32 = const -1082130432 @0
  %c4: f32 = const 2139095039 @0
  %c5: f32 = const -8388608 @0
  %c6: f32 = const 2143289344 @0
  %c7: f32 = const -4194303 @0
  %c8: f32 = const 2139095041 @0
  ret %c0, %c1, %c2, %c3, %c4, %c5, %c6, %c7, %c8 @0
}

func @one() -> f32 {
^entry:
  %c: f32 = const -4194303 @0
  ret %c @0
}

func @nan_is_unordered() -> i1, i1 {
^entry:
  %n: f32 = const 2139095041 @0
  %e: i1 = fcmp oeq %n, %n @0
  %u: i1 = fcmp uno %n, %n @0
  ret %e, %u @0
}

locs {
  @0 = unknown
}
