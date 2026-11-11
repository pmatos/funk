func @consts() -> f128, f128, f128, f128, f128, f128, f128, f128, f128 {
^entry:
  %c0: f128 = const 0.0 @0
  %c1: f128 = const -0.0 @0
  %c2: f128 = const 6.0e-4966 @0
  %c3: f128 = const -1.0 @0
  %c4: f128 = const 1.189731495357231765085759326628007e4932 @0
  %c5: f128 = const 0xffff0000000000000000000000000000 @0
  %c6: f128 = const 0x7fff8000000000000000000000000000 @0
  %c7: f128 = const 0xffff8000000000000000000000000001 @0
  %c8: f128 = const 0x7fff0000000000000000000000000001 @0
  ret %c0, %c1, %c2, %c3, %c4, %c5, %c6, %c7, %c8 @0
}

func @one() -> f128 {
^entry:
  %c: f128 = const 0xffff8000000000000000000000000001 @0
  ret %c @0
}

func @nan_is_unordered() -> i1, i1 {
^entry:
  %n: f128 = const 0x7fff0000000000000000000000000001 @0
  %e: i1 = fcmp oeq %n, %n @0
  %u: i1 = fcmp uno %n, %n @0
  ret %e, %u @0
}

locs {
  @0 = unknown
}
