func @add_i128(%x: i128, %y: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %t0: i128 = add %x, %one @0
  %t1: i128 = add %y, %t0 @0
  ret %t1 @0
}

locs {
  @0 = "llvm/test/CodeGen/X86/i128-add.ll":5:1 to 48:2
}
