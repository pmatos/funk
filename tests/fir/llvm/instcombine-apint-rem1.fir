func @test1(%X: i33) -> i33 {
^entry:
  %c: i33 = const 4096 @0
  %Y: i33 = urem %X, %c @0
  ret %Y @0
}

func @test1.folded(%X: i33) -> i33 {
^entry:
  %k: i33 = const 4095 @1
  %R: i33 = and %X, %k @1
  ret %R @1
}

func @test2(%X: i49) -> i49 {
^entry:
  %c: i49 = const 4096 @2
  %s: i49 = const 11 @2
  %tmp.0: i49 = shl %c, %s @2
  %Y: i49 = urem %X, %tmp.0 @2
  ret %Y @2
}

func @test2.folded(%X: i49) -> i49 {
^entry:
  %k: i49 = const 8388607 @3
  %R: i49 = and %X, %k @3
  ret %R @3
}

func @test3(%X: i59, %C: i1) -> i59 {
^entry:
  %a: i59 = const 70368744177664 @4
  %b: i59 = const 4096 @4
  %V: i59 = select %C, %a, %b @4
  %R: i59 = urem %X, %V @4
  ret %R @4
}

func @test3.folded(%X: i59, %C: i1) -> i59 {
^entry:
  %a: i59 = const 70368744177663 @5
  %b: i59 = const 4095 @5
  %V: i59 = select %C, %a, %b @5
  %R: i59 = and %X, %V @5
  ret %R @5
}

locs {
  @0 = "llvm/test/Transforms/InstCombine/apint-rem1.ll":7:1 to 10:2
  @1 = "llvm/test/Transforms/InstCombine/apint-rem1.ll":4:1 to 4:54
  @2 = "llvm/test/Transforms/InstCombine/apint-rem1.ll":12:1 to 16:2
  @3 = "llvm/test/Transforms/InstCombine/apint-rem1.ll":4:1 to 4:54
  @4 = "llvm/test/Transforms/InstCombine/apint-rem1.ll":18:1 to 22:2
  @5 = "llvm/test/Transforms/InstCombine/apint-rem1.ll":4:1 to 4:54
}
