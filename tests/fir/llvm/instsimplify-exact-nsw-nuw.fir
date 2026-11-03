func @div1(%V: i32) -> i32 {
^entry:
  %c: i32 = const -2147483648 @0
  %A: i32 = udiv %V, %c @0
  %B: i32 = udiv %A, %c @0
  ret %B @0
}

func @div2(%V: i32) -> i32 {
^entry:
  %m1: i32 = const -1 @1
  %A: i32 = sdiv %V, %m1 @1
  %c: i32 = const -2147483648 @1
  %B: i32 = sdiv %A, %c @1
  ret %B @1
}

func @shift2(%A: i32, %B: i32) -> i32 {
^entry:
  %C: i32 = lshr %A, %B @2
  %D: i32 = shl %C, %B @2
  ret %D @2
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/exact-nsw-nuw.ll":53:1 to 60:2
  @1 = "llvm/test/Transforms/InstSimplify/exact-nsw-nuw.ll":62:1 to 69:2
  @2 = "llvm/test/Transforms/InstSimplify/exact-nsw-nuw.ll":15:1 to 24:2
}
