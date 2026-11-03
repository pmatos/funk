func @PR23590(%x: i64) -> i64 {
^entry:
  %c: i64 = const 12345 @0
  %rem: i64 = urem %x, %c @0
  %c7: i64 = const 7 @0
  %div: i64 = udiv %rem, %c7 @0
  ret %div @0
}

func @PR38622(%0: i64) -> i64, i32 {
^entry:
  %c: i64 = const 4000000000 @1
  %2: i64 = udiv %0, %c @1
  %3: i64 = urem %0, %c @1
  %4: i32 = trunc %3 @1
  ret %2, %4 @1
}

func @PR38622_signed(%0: i64) -> i64, i32 {
^entry:
  %c: i64 = const 4000000000 @2
  %2: i64 = sdiv %0, %c @2
  %3: i64 = srem %0, %c @2
  %4: i32 = trunc %3 @2
  ret %2, %4 @2
}

func @urem_i64_3(%x: i64) -> i64 {
^entry:
  %k: i64 = const 3 @3
  %r: i64 = urem %x, %k @3
  ret %r @3
}

func @udiv_i64_3(%x: i64) -> i64 {
^entry:
  %k: i64 = const 3 @4
  %r: i64 = udiv %x, %k @4
  ret %r @4
}

func @urem_i64_5(%x: i64) -> i64 {
^entry:
  %k: i64 = const 5 @5
  %r: i64 = urem %x, %k @5
  ret %r @5
}

func @udiv_i64_5(%x: i64) -> i64 {
^entry:
  %k: i64 = const 5 @6
  %r: i64 = udiv %x, %k @6
  ret %r @6
}

func @urem_i64_17(%x: i64) -> i64 {
^entry:
  %k: i64 = const 17 @7
  %r: i64 = urem %x, %k @7
  ret %r @7
}

func @udiv_i64_17(%x: i64) -> i64 {
^entry:
  %k: i64 = const 17 @8
  %r: i64 = udiv %x, %k @8
  ret %r @8
}

func @urem_i64_255(%x: i64) -> i64 {
^entry:
  %k: i64 = const 255 @9
  %r: i64 = urem %x, %k @9
  ret %r @9
}

func @udiv_i64_255(%x: i64) -> i64 {
^entry:
  %k: i64 = const 255 @10
  %r: i64 = udiv %x, %k @10
  ret %r @10
}

func @urem_i64_65537(%x: i64) -> i64 {
^entry:
  %k: i64 = const 65537 @11
  %r: i64 = urem %x, %k @11
  ret %r @11
}

func @udiv_i64_65537(%x: i64) -> i64 {
^entry:
  %k: i64 = const 65537 @12
  %r: i64 = udiv %x, %k @12
  ret %r @12
}

func @urem_i64_12(%x: i64) -> i64 {
^entry:
  %k: i64 = const 12 @13
  %r: i64 = urem %x, %k @13
  ret %r @13
}

func @udiv_i64_12(%x: i64) -> i64 {
^entry:
  %k: i64 = const 12 @14
  %r: i64 = udiv %x, %k @14
  ret %r @14
}

func @udiv_i64_magic_large_postshift(%x: i64) -> i64 {
^entry:
  %k: i64 = const -4611686018427387906 @15
  %r: i64 = udiv %x, %k @15
  ret %r @15
}

func @urem_i64_magic_large_postshift(%x: i64) -> i64 {
^entry:
  %k: i64 = const -4611686018427387906 @16
  %r: i64 = urem %x, %k @16
  ret %r @16
}

func @udiv_i64_magic_large_preshift(%x: i64) -> i64 {
^entry:
  %k: i64 = const 60129542142 @17
  %r: i64 = udiv %x, %k @17
  ret %r @17
}

func @urem_i64_magic_large_preshift(%x: i64) -> i64 {
^entry:
  %k: i64 = const 60129542142 @18
  %r: i64 = urem %x, %k @18
  ret %r @18
}

func @udiv_i64_magic_is_add(%x: i64) -> i64 {
^entry:
  %k: i64 = const 844429225099263 @19
  %r: i64 = udiv %x, %k @19
  ret %r @19
}

func @urem_i64_magic_is_add(%x: i64) -> i64 {
^entry:
  %k: i64 = const 844429225099263 @20
  %r: i64 = urem %x, %k @20
  ret %r @20
}

locs {
  @0 = "llvm/test/CodeGen/X86/divide-by-constant.ll":294:1 to 402:2
  @1 = "llvm/test/CodeGen/X86/divide-by-constant.ll":404:1 to 472:2
  @2 = "llvm/test/CodeGen/X86/divide-by-constant.ll":474:1 to 527:2
  @3 = "llvm/test/CodeGen/X86/divide-by-constant.ll":529:1 to 558:2
  @4 = "llvm/test/CodeGen/X86/divide-by-constant.ll":843:1 to 884:2
  @5 = "llvm/test/CodeGen/X86/divide-by-constant.ll":560:1 to 589:2
  @6 = "llvm/test/CodeGen/X86/divide-by-constant.ll":886:1 to 927:2
  @7 = "llvm/test/CodeGen/X86/divide-by-constant.ll":624:1 to 657:2
  @8 = "llvm/test/CodeGen/X86/divide-by-constant.ll":972:1 to 1015:2
  @9 = "llvm/test/CodeGen/X86/divide-by-constant.ll":659:1 to 695:2
  @10 = "llvm/test/CodeGen/X86/divide-by-constant.ll":1017:1 to 1058:2
  @11 = "llvm/test/CodeGen/X86/divide-by-constant.ll":770:1 to 802:2
  @12 = "llvm/test/CodeGen/X86/divide-by-constant.ll":1150:1 to 1194:2
  @13 = "llvm/test/CodeGen/X86/divide-by-constant.ll":804:1 to 841:2
  @14 = "llvm/test/CodeGen/X86/divide-by-constant.ll":1196:1 to 1239:2
  @15 = "llvm/test/CodeGen/X86/divide-by-constant.ll":1242:1 to 1292:2
  @16 = "llvm/test/CodeGen/X86/divide-by-constant.ll":1295:1 to 1360:2
  @17 = "llvm/test/CodeGen/X86/divide-by-constant.ll":1363:1 to 1418:2
  @18 = "llvm/test/CodeGen/X86/divide-by-constant.ll":1421:1 to 1491:2
  @19 = "llvm/test/CodeGen/X86/divide-by-constant.ll":1494:1 to 1556:2
  @20 = "llvm/test/CodeGen/X86/divide-by-constant.ll":1559:1 to 1636:2
}
