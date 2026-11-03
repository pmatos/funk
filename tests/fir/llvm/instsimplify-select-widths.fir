func @select_icmp_trunc_8_eq_0_and_not_8(%x: i32) -> i32 {
^entry:
  %trunc: i4 = trunc %x @0
  %m1: i4 = const -1 @0
  %cmp: i1 = icmp sgt %trunc, %m1 @0
  %c: i32 = const -9 @0
  %and: i32 = and %x, %c @0
  %sel: i32 = select %cmp, %x, %and @0
  ret %sel @0
}

func @select_icmp_trunc_8_eq_0_and_not_8.folded(%x: i32) -> i32 {
^entry:
  %c: i32 = const -9 @1
  %and: i32 = and %x, %c @1
  ret %and @1
}

func @select_icmp_trunc_8_ne_0_and_not_8(%x: i32) -> i32 {
^entry:
  %trunc: i4 = trunc %x @2
  %z: i4 = const 0 @2
  %cmp: i1 = icmp slt %trunc, %z @2
  %c: i32 = const -9 @2
  %and: i32 = and %x, %c @2
  %sel: i32 = select %cmp, %x, %and @2
  ret %sel @2
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/select.ll":519:1 to 529:2
  @1 = "llvm/test/Transforms/InstSimplify/select.ll":520:1 to 522:33
  @2 = "llvm/test/Transforms/InstSimplify/select.ll":543:1 to 552:2
}
