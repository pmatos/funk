func @negated_operand(%x: i32) -> i32 {
^entry:
  %z: i32 = const 0 @0
  %negx: i32 = sub nsw %z, %x @0
  %div: i32 = sdiv %negx, %x @0
  ret %div @0
}

func @knownnegation(%x: i32, %y: i32) -> i32 {
^entry:
  %xy: i32 = sub nsw %x, %y @1
  %yx: i32 = sub nsw %y, %x @1
  %div: i32 = sdiv %xy, %yx @1
  ret %div @1
}

func @negated_operand_2(%t: i32) -> i32 {
^entry:
  %c5: i32 = const 5 @2
  %x: i32 = sub %t, %c5 @2
  %z: i32 = const 0 @2
  %negx: i32 = sub nsw %z, %x @2
  %div: i32 = sdiv %negx, %x @2
  ret %div @2
}

func @negated_operand_commute(%x: i32) -> i32 {
^entry:
  %z: i32 = const 0 @3
  %negx: i32 = sub nsw %z, %x @3
  %div: i32 = sdiv %x, %negx @3
  ret %div @3
}

func @negated_operand_bad(%x: i32) -> i32 {
^entry:
  %z: i32 = const 0 @4
  %negx: i32 = sub %z, %x @4
  %div: i32 = sdiv %negx, %x @4
  ret %div @4
}

func @knownnegation_bad_3(%x: i32, %y: i32) -> i32 {
^entry:
  %xy: i32 = sub %x, %y @5
  %yx: i32 = sub %y, %x @5
  %div: i32 = sdiv %xy, %yx @5
  ret %div @5
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/sdiv.ll":4:1 to 11:2
  @1 = "llvm/test/Transforms/InstSimplify/sdiv.ll":22:1 to 30:2
  @2 = "llvm/test/Transforms/InstSimplify/sdiv.ll":42:1 to 50:2
  @3 = "llvm/test/Transforms/InstSimplify/sdiv.ll":52:1 to 59:2
  @4 = "llvm/test/Transforms/InstSimplify/sdiv.ll":61:1 to 70:2
  @5 = "llvm/test/Transforms/InstSimplify/sdiv.ll":98:1 to 109:2
}
