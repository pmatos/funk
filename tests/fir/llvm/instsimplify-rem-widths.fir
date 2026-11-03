func @srem_mul_sdiv(%x: i4, %y: i4) -> i4 {
^entry:
  %d: i4 = sdiv %x, %y @0
  %mul: i4 = mul %d, %y @0
  %mod: i4 = srem %mul, %y @0
  ret %mod @0
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/rem.ll":450:1 to 458:2
}
