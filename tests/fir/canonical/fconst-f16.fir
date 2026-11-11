func @consts() -> f16, f16, f16, f16, f16, f16, f16, f16, f16 {
^entry:
  %c0: f16 = const 0.0 @0
  %c1: f16 = const -0.0 @0
  %c2: f16 = const 6.0e-8 @0
  %c3: f16 = const -1.0 @0
  %c4: f16 = const 65500.0 @0
  %c5: f16 = const 0xfc00 @0
  %c6: f16 = const 0x7e00 @0
  %c7: f16 = const 0xfe01 @0
  %c8: f16 = const 0x7c01 @0
  ret %c0, %c1, %c2, %c3, %c4, %c5, %c6, %c7, %c8 @0
}

func @one() -> f16 {
^entry:
  %c: f16 = const 0xfe01 @0
  ret %c @0
}

func @nan_is_unordered() -> i1, i1 {
^entry:
  %n: f16 = const 0x7c01 @0
  %e: i1 = fcmp oeq %n, %n @0
  %u: i1 = fcmp uno %n, %n @0
  ret %e, %u @0
}

locs {
  @0 = unknown
}
