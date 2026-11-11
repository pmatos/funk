func @consts() -> f64, f64, f64, f64, f64, f64, f64, f64, f64 {
^entry:
  %c0: f64 = const 0 @0
  %c1: f64 = const -9223372036854775808 @0
  %c2: f64 = const 1 @0
  %c3: f64 = const -4616189618054758400 @0
  %c4: f64 = const 9218868437227405311 @0
  %c5: f64 = const -4503599627370496 @0
  %c6: f64 = const 9221120237041090560 @0
  %c7: f64 = const -2251799813685247 @0
  %c8: f64 = const 9218868437227405313 @0
  ret %c0, %c1, %c2, %c3, %c4, %c5, %c6, %c7, %c8 @0
}

func @one() -> f64 {
^entry:
  %c: f64 = const -2251799813685247 @0
  ret %c @0
}

func @nan_is_unordered() -> i1, i1 {
^entry:
  %n: f64 = const 9218868437227405313 @0
  %e: i1 = fcmp oeq %n, %n @0
  %u: i1 = fcmp uno %n, %n @0
  ret %e, %u @0
}

locs {
  @0 = unknown
}
