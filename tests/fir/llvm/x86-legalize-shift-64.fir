func @test1(%xx: i32, %test: i32) -> i64 {
^entry:
  %conv: i64 = zext %xx @0
  %c7: i32 = const 7 @0
  %and: i32 = and %test, %c7 @0
  %sh_prom: i64 = zext %and @0
  %r: i64 = shl %conv, %sh_prom @0
  ret %r @0
}

func @test2(%xx: i64, %test: i32) -> i64 {
^entry:
  %c7: i32 = const 7 @1
  %and: i32 = and %test, %c7 @1
  %sh_prom: i64 = zext %and @1
  %r: i64 = shl %xx, %sh_prom @1
  ret %r @1
}

func @test3(%xx: i64, %test: i32) -> i64 {
^entry:
  %c7: i32 = const 7 @2
  %and: i32 = and %test, %c7 @2
  %sh_prom: i64 = zext %and @2
  %r: i64 = lshr %xx, %sh_prom @2
  ret %r @2
}

func @test4(%xx: i64, %test: i32) -> i64 {
^entry:
  %c7: i32 = const 7 @3
  %and: i32 = and %test, %c7 @3
  %sh_prom: i64 = zext %and @3
  %r: i64 = ashr %xx, %sh_prom @3
  ret %r @3
}

locs {
  @0 = "llvm/test/CodeGen/X86/legalize-shift-64.ll":4:1 to 21:2
  @1 = "llvm/test/CodeGen/X86/legalize-shift-64.ll":23:1 to 40:2
  @2 = "llvm/test/CodeGen/X86/legalize-shift-64.ll":42:1 to 56:2
  @3 = "llvm/test/CodeGen/X86/legalize-shift-64.ll":58:1 to 72:2
}
