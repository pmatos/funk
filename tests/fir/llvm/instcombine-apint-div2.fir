func @test1(%X: i333) -> i333 {
^entry:
  %c: i333 = const 70368744177664 @0
  %Y: i333 = udiv %X, %c @0
  ret %Y @0
}

func @test1.folded(%X: i333) -> i333 {
^entry:
  %k: i333 = const 46 @1
  %R: i333 = lshr %X, %k @1
  ret %R @1
}

func @test2(%X: i499) -> i499 {
^entry:
  %c: i499 = const 4096 @2
  %s: i499 = const 197 @2
  %tmp.0: i499 = shl %c, %s @2
  %Y: i499 = udiv %X, %tmp.0 @2
  ret %Y @2
}

func @test2.folded(%X: i499) -> i499 {
^entry:
  %k: i499 = const 209 @3
  %R: i499 = lshr %X, %k @3
  ret %R @3
}

func @test3(%X: i599, %C: i1) -> i599 {
^entry:
  %a: i599 = const 70368744177664 @4
  %b: i599 = const 4096 @4
  %V: i599 = select %C, %a, %b @4
  %R: i599 = udiv %X, %V @4
  ret %R @4
}

func @test3.folded(%X: i599, %C: i1) -> i599 {
^entry:
  %a: i599 = const 46 @5
  %b: i599 = const 12 @5
  %V: i599 = select %C, %a, %b @5
  %R: i599 = lshr %X, %V @5
  ret %R @5
}

locs {
  @0 = "llvm/test/Transforms/InstCombine/apint-div2.ll":7:1 to 10:2
  @1 = "llvm/test/Transforms/InstCombine/apint-div2.ll":4:1 to 4:54
  @2 = "llvm/test/Transforms/InstCombine/apint-div2.ll":12:1 to 16:2
  @3 = "llvm/test/Transforms/InstCombine/apint-div2.ll":4:1 to 4:54
  @4 = "llvm/test/Transforms/InstCombine/apint-div2.ll":18:1 to 22:2
  @5 = "llvm/test/Transforms/InstCombine/apint-div2.ll":4:1 to 4:54
}
