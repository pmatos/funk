func @test1(%V: i1) -> i1 {
^entry:
  %Z: i32 = zext %V @0
  %T: i1 = trunc %Z @0
  ret %T @0
}

func @zext_of_trunc_no_flag(%x: i64) -> i64 {
^entry:
  %t: i32 = trunc %x @1
  %z: i64 = zext %t @1
  ret %z @1
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/cast.ll":5:1 to 14:2
  @1 = "llvm/test/Transforms/InstSimplify/cast.ll":91:1 to 100:2
}
