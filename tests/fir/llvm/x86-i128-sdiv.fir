func @test1(%x: i128) -> i128 {
^entry:
  %c: i128 = const 73786976294838206464 @0
  %tmp: i128 = sdiv %x, %c @0
  ret %tmp @0
}

func @test2(%x: i128) -> i128 {
^entry:
  %c: i128 = const -73786976294838206464 @1
  %tmp: i128 = sdiv %x, %c @1
  ret %tmp @1
}

func @test3(%x: i128) -> i128 {
^entry:
  %c: i128 = const -73786976294838206467 @2
  %tmp: i128 = sdiv %x, %c @2
  ret %tmp @2
}

locs {
  @0 = "llvm/test/CodeGen/X86/i128-sdiv.ll":8:1 to 55:2
  @1 = "llvm/test/CodeGen/X86/i128-sdiv.ll":57:1 to 117:2
  @2 = "llvm/test/CodeGen/X86/i128-sdiv.ll":119:1 to 134:2
}
