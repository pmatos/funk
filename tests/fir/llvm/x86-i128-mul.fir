func @foo(%x: i64, %y: i64) -> i64 {
^entry:
  %tmp0: i128 = zext %x @0
  %tmp1: i128 = zext %y @0
  %tmp2: i128 = mul %tmp0, %tmp1 @0
  %c: i32 = const 64 @0
  %tmp7: i128 = zext %c @0
  %tmp3: i128 = lshr %tmp2, %tmp7 @0
  %tmp4: i64 = trunc %tmp3 @0
  ret %tmp4 @0
}

locs {
  @0 = "llvm/test/CodeGen/X86/i128-mul.ll":9:1 to 96:2
}
