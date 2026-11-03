func @shl_by_0(%A: i47) -> i47 {
^entry:
  %c: i47 = const 0 @0
  %B: i47 = shl %A, %c @0
  ret %B @0
}

func @shl_0(%X: i41) -> i41 {
^entry:
  %c: i41 = const 0 @1
  %B: i41 = shl %c, %X @1
  ret %B @1
}

func @ashr_by_0(%A: i41) -> i41 {
^entry:
  %c: i41 = const 0 @2
  %B: i41 = ashr %A, %c @2
  ret %B @2
}

func @ashr_0(%X: i39) -> i39 {
^entry:
  %c: i39 = const 0 @3
  %B: i39 = ashr %c, %X @3
  ret %B @3
}

func @lshr_by_bitwidth(%A: i55) -> i55 {
^entry:
  %c: i55 = const 55 @4
  %B: i55 = lshr %A, %c @4
  ret %B @4
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/shift.ll":4:1 to 10:2
  @1 = "llvm/test/Transforms/InstSimplify/shift.ll":12:1 to 18:2
  @2 = "llvm/test/Transforms/InstSimplify/shift.ll":28:1 to 34:2
  @3 = "llvm/test/Transforms/InstSimplify/shift.ll":36:1 to 42:2
  @4 = "llvm/test/Transforms/InstSimplify/shift.ll":52:1 to 58:2
}
