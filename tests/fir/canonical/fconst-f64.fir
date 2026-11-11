func @consts() -> f64, f64, f64, f64, f64, f64, f64, f64, f64 {
^entry:
  %c0: f64 = const 0.0 @0
  %c1: f64 = const -0.0 @0
  %c2: f64 = const 5.0e-324 @0
  %c3: f64 = const -1.0 @0
  %c4: f64 = const 1.7976931348623157e308 @0
  %c5: f64 = const 0xfff0000000000000 @0
  %c6: f64 = const 0x7ff8000000000000 @0
  %c7: f64 = const 0xfff8000000000001 @0
  %c8: f64 = const 0x7ff0000000000001 @0
  ret %c0, %c1, %c2, %c3, %c4, %c5, %c6, %c7, %c8 @0
}

func @one() -> f64 {
^entry:
  %c: f64 = const 0xfff8000000000001 @0
  ret %c @0
}

func @nan_is_unordered() -> i1, i1 {
^entry:
  %n: f64 = const 0x7ff0000000000001 @0
  %e: i1 = fcmp oeq %n, %n @0
  %u: i1 = fcmp uno %n, %n @0
  ret %e, %u @0
}

locs {
  @0 = unknown
}
