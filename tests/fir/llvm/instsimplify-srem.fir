func @negated_operand(%x: i32) -> i32 {
^entry:
  %z: i32 = const 0 @0
  %negx: i32 = sub %z, %x @0
  %rem: i32 = srem %negx, %x @0
  ret %rem @0
}

func @knownnegation(%x: i32, %y: i32) -> i32 {
^entry:
  %xy: i32 = sub %x, %y @1
  %yx: i32 = sub %y, %x @1
  %rem: i32 = srem %xy, %yx @1
  ret %rem @1
}

func @negated_operand_commute(%x: i32) -> i32 {
^entry:
  %z: i32 = const 0 @2
  %negx: i32 = sub %z, %x @2
  %rem: i32 = srem %x, %negx @2
  ret %rem @2
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/srem.ll":4:1 to 11:2
  @1 = "llvm/test/Transforms/InstSimplify/srem.ll":22:1 to 30:2
  @2 = "llvm/test/Transforms/InstSimplify/srem.ll":62:1 to 69:2
}
