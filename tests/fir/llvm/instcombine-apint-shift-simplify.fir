func @test0(%A: i41, %B: i41, %C: i41) -> i41 {
^entry:
  %X: i41 = shl %A, %C @0
  %Y: i41 = shl %B, %C @0
  %Z: i41 = and %X, %Y @0
  ret %Z @0
}

func @test0.folded(%A: i41, %B: i41, %C: i41) -> i41 {
^entry:
  %t: i41 = and %A, %B @1
  %Z: i41 = shl %t, %C @1
  ret %Z @1
}

func @test1(%A: i57, %B: i57, %C: i57) -> i57 {
^entry:
  %X: i57 = lshr %A, %C @2
  %Y: i57 = lshr %B, %C @2
  %Z: i57 = or %X, %Y @2
  ret %Z @2
}

func @test1.folded(%A: i57, %B: i57, %C: i57) -> i57 {
^entry:
  %t: i57 = or %A, %B @3
  %Z: i57 = lshr %t, %C @3
  ret %Z @3
}

func @test2(%A: i49, %B: i49, %C: i49) -> i49 {
^entry:
  %X: i49 = ashr %A, %C @4
  %Y: i49 = ashr %B, %C @4
  %Z: i49 = xor %X, %Y @4
  ret %Z @4
}

func @test2.folded(%A: i49, %B: i49, %C: i49) -> i49 {
^entry:
  %t: i49 = xor %A, %B @5
  %Z: i49 = ashr %t, %C @5
  ret %Z @5
}

locs {
  @0 = "llvm/test/Transforms/InstCombine/apint-shift-simplify.ll":3:1 to 12:2
  @1 = "llvm/test/Transforms/InstCombine/apint-shift-simplify.ll":8:1 to 11:18
  @2 = "llvm/test/Transforms/InstCombine/apint-shift-simplify.ll":14:1 to 23:2
  @3 = "llvm/test/Transforms/InstCombine/apint-shift-simplify.ll":19:1 to 22:18
  @4 = "llvm/test/Transforms/InstCombine/apint-shift-simplify.ll":25:1 to 34:2
  @5 = "llvm/test/Transforms/InstCombine/apint-shift-simplify.ll":30:1 to 33:18
}
