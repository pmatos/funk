func @test1(%x: i16) -> i16 {
^entry:
  %k: i16 = const 33 @0
  %r: i16 = udiv %x, %k @0
  ret %r @0
}

func @test2(%x: i8, %c: i16) -> i16 {
^entry:
  %k: i16 = const 3 @1
  %r: i16 = udiv %c, %k @1
  ret %r @1
}

func @test3(%x: i8, %c: i8) -> i8 {
^entry:
  %k: i8 = const 3 @2
  %r: i8 = udiv %c, %k @2
  ret %r @2
}

func @test4(%x: i16) -> i16 {
^entry:
  %k: i16 = const 33 @3
  %r: i16 = sdiv %x, %k @3
  ret %r @3
}

func @test5(%x: i32) -> i32 {
^entry:
  %k: i32 = const 1577682821 @4
  %r: i32 = udiv %x, %k @4
  ret %r @4
}

func @test6(%x: i16) -> i16 {
^entry:
  %k: i16 = const 10 @5
  %r: i16 = sdiv %x, %k @5
  ret %r @5
}

func @test7(%x: i32) -> i32 {
^entry:
  %k: i32 = const 28 @6
  %r: i32 = udiv %x, %k @6
  ret %r @6
}

func @test8(%x: i8) -> i8 {
^entry:
  %k: i8 = const 78 @7
  %r: i8 = udiv %x, %k @7
  ret %r @7
}

func @test9(%x: i8) -> i8 {
^entry:
  %k: i8 = const 116 @8
  %r: i8 = udiv %x, %k @8
  ret %r @8
}

func @testsize1(%x: i32) -> i32 {
^entry:
  %k: i32 = const 32 @9
  %r: i32 = sdiv %x, %k @9
  ret %r @9
}

func @testsize2(%x: i32) -> i32 {
^entry:
  %k: i32 = const 33 @10
  %r: i32 = sdiv %x, %k @10
  ret %r @10
}

func @testsize3(%x: i32) -> i32 {
^entry:
  %k: i32 = const 32 @11
  %r: i32 = udiv %x, %k @11
  ret %r @11
}

func @testsize4(%x: i32) -> i32 {
^entry:
  %k: i32 = const 33 @12
  %r: i32 = udiv %x, %k @12
  ret %r @12
}

locs {
  @0 = "llvm/test/CodeGen/X86/divide-by-constant.ll":6:1 to 24:2
  @1 = "llvm/test/CodeGen/X86/divide-by-constant.ll":26:1 to 45:2
  @2 = "llvm/test/CodeGen/X86/divide-by-constant.ll":47:1 to 65:2
  @3 = "llvm/test/CodeGen/X86/divide-by-constant.ll":67:1 to 91:2
  @4 = "llvm/test/CodeGen/X86/divide-by-constant.ll":93:1 to 111:2
  @5 = "llvm/test/CodeGen/X86/divide-by-constant.ll":113:1 to 137:2
  @6 = "llvm/test/CodeGen/X86/divide-by-constant.ll":139:1 to 159:2
  @7 = "llvm/test/CodeGen/X86/divide-by-constant.ll":162:1 to 183:2
  @8 = "llvm/test/CodeGen/X86/divide-by-constant.ll":185:1 to 206:2
  @9 = "llvm/test/CodeGen/X86/divide-by-constant.ll":208:1 to 229:2
  @10 = "llvm/test/CodeGen/X86/divide-by-constant.ll":231:1 to 252:2
  @11 = "llvm/test/CodeGen/X86/divide-by-constant.ll":254:1 to 269:2
  @12 = "llvm/test/CodeGen/X86/divide-by-constant.ll":271:1 to 292:2
}
