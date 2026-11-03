func @test1(%x: i128) -> i128 {
^entry:
  %c: i128 = const 73786976294838206464 @0
  %r: i128 = udiv %x, %c @0
  ret %r @0
}

func @test2(%x: i128) -> i128 {
^entry:
  %c: i128 = const -73786976294838206464 @1
  %r: i128 = udiv %x, %c @1
  ret %r @1
}

func @test3(%x: i128) -> i128 {
^entry:
  %c: i128 = const -73786976294838206467 @2
  %r: i128 = udiv %x, %c @2
  ret %r @2
}

func @div_by_7(%x: i128) -> i128 {
^entry:
  %c: i128 = const 7 @3
  %r: i128 = udiv %x, %c @3
  ret %r @3
}

func @div_by_11(%x: i128) -> i128 {
^entry:
  %c: i128 = const 11 @4
  %r: i128 = udiv %x, %c @4
  ret %r @4
}

func @div_by_22(%x: i128) -> i128 {
^entry:
  %c: i128 = const 22 @5
  %r: i128 = udiv %x, %c @5
  ret %r @5
}

func @div_by_56(%x: i128) -> i128 {
^entry:
  %c: i128 = const 56 @6
  %r: i128 = udiv %x, %c @6
  ret %r @6
}

func @rem_by_7(%x: i128) -> i128 {
^entry:
  %c: i128 = const 7 @7
  %r: i128 = urem %x, %c @7
  ret %r @7
}

func @rem_by_14(%x: i128) -> i128 {
^entry:
  %c: i128 = const 14 @8
  %r: i128 = urem %x, %c @8
  ret %r @8
}

func @div_by_67(%x: i128) -> i128 {
^entry:
  %c: i128 = const 67 @9
  %r: i128 = udiv %x, %c @9
  ret %r @9
}

locs {
  @0 = "llvm/test/CodeGen/X86/i128-udiv.ll":5:1 to 33:2
  @1 = "llvm/test/CodeGen/X86/i128-udiv.ll":37:1 to 349:2
  @2 = "llvm/test/CodeGen/X86/i128-udiv.ll":352:1 to 680:2
  @3 = "llvm/test/CodeGen/X86/i128-udiv.ll":682:1 to 1006:2
  @4 = "llvm/test/CodeGen/X86/i128-udiv.ll":1008:1 to 1330:2
  @5 = "llvm/test/CodeGen/X86/i128-udiv.ll":1332:1 to 1656:2
  @6 = "llvm/test/CodeGen/X86/i128-udiv.ll":1658:1 to 1982:2
  @7 = "llvm/test/CodeGen/X86/i128-udiv.ll":1984:1 to 2316:2
  @8 = "llvm/test/CodeGen/X86/i128-udiv.ll":2318:1 to 2653:2
  @9 = "llvm/test/CodeGen/X86/i128-udiv.ll":2655:1 to 2984:2
}
