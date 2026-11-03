func @test1(%X: i17) -> i17 {
^entry:
  %c: i17 = const 1024 @0
  %Y: i17 = mul %X, %c @0
  ret %Y @0
}

func @test1.folded(%X: i17) -> i17 {
^entry:
  %c: i17 = const 10 @1
  %Y: i17 = shl %X, %c @1
  ret %Y @1
}

locs {
  @0 = "llvm/test/Transforms/InstCombine/apint-mul1.ll":7:1 to 14:2
  @1 = "llvm/test/Transforms/InstCombine/apint-mul1.ll":8:1 to 10:31
}
