func @test_lshr_i128(%x: i128, %a: i128) -> i128 {
^entry:
  %0: i128 = lshr %x, %a @0
  ret %0 @0
}

func @test_ashr_i128(%x: i128, %a: i128) -> i128 {
^entry:
  %0: i128 = ashr %x, %a @1
  ret %0 @1
}

func @test_shl_i128(%x: i128, %a: i128) -> i128 {
^entry:
  %0: i128 = shl %x, %a @2
  ret %0 @2
}

func @test_lshr_i128_outofrange(%x: i128) -> i128 {
^entry:
  %m1: i128 = const -1 @3
  %0: i128 = lshr %x, %m1 @3
  ret %0 @3
}

func @test_ashr_i128_outofrange(%x: i128) -> i128 {
^entry:
  %m1: i128 = const -1 @4
  %0: i128 = ashr %x, %m1 @4
  ret %0 @4
}

func @test_shl_i128_outofrange(%x: i128) -> i128 {
^entry:
  %m1: i128 = const -1 @5
  %0: i128 = shl %x, %m1 @5
  ret %0 @5
}

func @lshr_shl_mask(%a0: i128) -> i128 {
^entry:
  %c1: i128 = const 1 @6
  %1: i128 = shl %a0, %c1 @6
  %2: i128 = lshr %1, %c1 @6
  ret %2 @6
}

func @shift_i128_limited_shamt(%a: i128, %b: i32) -> i128 {
^start:
  %c6: i32 = const 6 @7
  %shamt: i32 = sub nuw nsw %c6, %b @7
  %ext: i128 = zext %shamt @7
  %res: i128 = shl %a, %ext @7
  ret %res @7
}

func @shift_i128_limited_shamt_no_nuw(%a: i128, %b: i32) -> i128 {
^start:
  %c6: i32 = const 6 @8
  %shamt: i32 = sub nsw %c6, %b @8
  %ext: i128 = zext %shamt @8
  %res: i128 = shl %a, %ext @8
  ret %res @8
}

func @shift_i128_limited_shamt_unknown_lhs(%a: i128, %b: i32, %c: i32) -> i128 {
^start:
  %shamt: i32 = sub nuw nsw %c, %b @9
  %ext: i128 = zext %shamt @9
  %res: i128 = shl %a, %ext @9
  ret %res @9
}

locs {
  @0 = "llvm/test/CodeGen/X86/shift-i128.ll":9:1 to 73:2
  @1 = "llvm/test/CodeGen/X86/shift-i128.ll":75:1 to 141:2
  @2 = "llvm/test/CodeGen/X86/shift-i128.ll":143:1 to 209:2
  @3 = "llvm/test/CodeGen/X86/shift-i128.ll":211:1 to 228:2
  @4 = "llvm/test/CodeGen/X86/shift-i128.ll":230:1 to 247:2
  @5 = "llvm/test/CodeGen/X86/shift-i128.ll":249:1 to 266:2
  @6 = "llvm/test/CodeGen/X86/shift-i128.ll":897:1 to 936:2
  @7 = "llvm/test/CodeGen/X86/shift-i128.ll":938:1 to 996:2
  @8 = "llvm/test/CodeGen/X86/shift-i128.ll":998:1 to 1068:2
  @9 = "llvm/test/CodeGen/X86/shift-i128.ll":1070:1 to 1139:2
}
