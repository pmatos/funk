func @consts() -> f32, f32, f32, f32, f32, f32, f32, f32, f32 {
^entry:
  %c0: f32 = const 0.0 @0
  %c1: f32 = const -0.0 @0
  %c2: f32 = const 1.0e-45 @0
  %c3: f32 = const -1.0 @0
  %c4: f32 = const 3.4028235e38 @0
  %c5: f32 = const 0xff800000 @0
  %c6: f32 = const 0x7fc00000 @0
  %c7: f32 = const 0xffc00001 @0
  %c8: f32 = const 0x7f800001 @0
  ret %c0, %c1, %c2, %c3, %c4, %c5, %c6, %c7, %c8 @0
}

func @one() -> f32 {
^entry:
  %c: f32 = const 0xffc00001 @0
  ret %c @0
}

func @nan_is_unordered() -> i1, i1 {
^entry:
  %n: f32 = const 0x7f800001 @0
  %e: i1 = fcmp oeq %n, %n @0
  %u: i1 = fcmp uno %n, %n @0
  ret %e, %u @0
}

locs {
  @0 = unknown
}
