func @consts() -> bf16, bf16, bf16, bf16, bf16, bf16, bf16, bf16, bf16 {
^entry:
  %c0: bf16 = const 0 @0
  %c1: bf16 = const -32768 @0
  %c2: bf16 = const 1 @0
  %c3: bf16 = const -16512 @0
  %c4: bf16 = const 32639 @0
  %c5: bf16 = const -128 @0
  %c6: bf16 = const 32704 @0
  %c7: bf16 = const -63 @0
  %c8: bf16 = const 32641 @0
  ret %c0, %c1, %c2, %c3, %c4, %c5, %c6, %c7, %c8 @0
}

func @one() -> bf16 {
^entry:
  %c: bf16 = const -63 @0
  ret %c @0
}

func @nan_is_unordered() -> i1, i1 {
^entry:
  %n: bf16 = const 32641 @0
  %e: i1 = fcmp oeq %n, %n @0
  %u: i1 = fcmp uno %n, %n @0
  ret %e, %u @0
}

locs {
  @0 = unknown
}
