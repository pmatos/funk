func @test1(%x: i1) -> i1 {
^entry:
  %c: i1 = const true @0
  %tmp.2: i1 = xor %x, %c @0
  %tmp.4: i1 = add %tmp.2, %c @0
  ret %tmp.4 @0
}

func @test2(%x: i47) -> i47 {
^entry:
  %c: i47 = const -70368744177664 @1
  %tmp.2: i47 = xor %x, %c @1
  %tmp.4: i47 = add %tmp.2, %c @1
  ret %tmp.4 @1
}

func @test3(%x: i15) -> i15 {
^entry:
  %c: i15 = const -16384 @2
  %tmp.2: i15 = xor %x, %c @2
  %tmp.4: i15 = add %tmp.2, %c @2
  ret %tmp.4 @2
}

func @test4(%x: i49) -> i49 {
^entry:
  %c: i49 = const -2 @3
  %tmp.2: i49 = and %x, %c @3
  %one: i49 = const 1 @3
  %tmp.4: i49 = add %tmp.2, %one @3
  ret %tmp.4 @3
}

func @test4.folded(%x: i49) -> i49 {
^entry:
  %one: i49 = const 1 @4
  %tmp.4: i49 = or %x, %one @4
  ret %tmp.4 @4
}

func @sext(%x: i4) -> i7 {
^entry:
  %c: i4 = const -8 @5
  %xor: i4 = xor %x, %c @5
  %zext: i7 = zext %xor @5
  %d: i7 = const -8 @5
  %add: i7 = add nsw %zext, %d @5
  ret %add @5
}

func @sext.folded(%x: i4) -> i7 {
^entry:
  %add: i7 = sext %x @6
  ret %add @6
}

func @sext_multiuse(%x: i4) -> i4 {
^entry:
  %c: i4 = const -8 @7
  %xor: i4 = xor %x, %c @7
  %zext: i7 = zext %xor @7
  %d: i7 = const -8 @7
  %add: i7 = add nsw %zext, %d @7
  %mul: i7 = sdiv %zext, %add @7
  %trunc: i4 = trunc %mul @7
  %div: i4 = sdiv %trunc, %xor @7
  ret %div @7
}

func @sext_multiuse.folded(%x: i4) -> i4 {
^entry:
  %c: i4 = const -8 @8
  %xor: i4 = xor %x, %c @8
  %zext: i7 = zext %xor @8
  %add: i7 = sext %x @8
  %mul: i7 = sdiv %zext, %add @8
  %trunc: i4 = trunc %mul @8
  %div: i4 = sdiv %trunc, %xor @8
  ret %div @8
}

func @test5(%x: i111) -> i111 {
^entry:
  %one: i111 = const 1 @9
  %top: i111 = const 110 @9
  %tmp.2: i111 = shl %one, %top @9
  %tmp.4: i111 = xor %x, %tmp.2 @9
  %tmp.6: i111 = add %tmp.4, %tmp.2 @9
  ret %tmp.6 @9
}

func @test6(%x: i65) -> i65 {
^entry:
  %one: i65 = const 1 @10
  %top: i65 = const 64 @10
  %tmp.0: i65 = shl %one, %top @10
  %tmp.2: i65 = xor %x, %tmp.0 @10
  %tmp.4: i65 = add %tmp.2, %tmp.0 @10
  ret %tmp.4 @10
}

func @test7(%x: i1024) -> i1024 {
^entry:
  %one: i1024 = const 1 @11
  %top: i1024 = const 1023 @11
  %tmp.0: i1024 = shl %one, %top @11
  %tmp.2: i1024 = xor %x, %tmp.0 @11
  %tmp.4: i1024 = add %tmp.2, %tmp.0 @11
  ret %tmp.4 @11
}

func @test8(%x: i128) -> i128 {
^entry:
  %one: i128 = const 1 @12
  %c127: i128 = const 127 @12
  %tmp.5: i128 = shl %one, %c127 @12
  %c120: i128 = const 120 @12
  %tmp.1: i128 = ashr %tmp.5, %c120 @12
  %tmp.2: i128 = xor %x, %tmp.1 @12
  %tmp.4: i128 = add %tmp.2, %tmp.5 @12
  ret %tmp.4 @12
}

func @test8.folded(%x: i128) -> i128 {
^entry:
  %c: i128 = const 170141183460469231731687303715884105600 @13
  %tmp.4: i128 = xor %x, %c @13
  ret %tmp.4 @13
}

func @test9(%x: i77) -> i77 {
^entry:
  %c: i77 = const 562949953421310 @14
  %tmp.2: i77 = and %x, %c @14
  %one: i77 = const 1 @14
  %tmp.4: i77 = add %tmp.2, %one @14
  ret %tmp.4 @14
}

func @test9.folded(%x: i77) -> i77 {
^entry:
  %c: i77 = const 562949953421310 @15
  %tmp.2: i77 = and %x, %c @15
  %one: i77 = const 1 @15
  %tmp.4: i77 = or %tmp.2, %one @15
  ret %tmp.4 @15
}

locs {
  @0 = "llvm/test/Transforms/InstCombine/apint-add.ll":7:1 to 14:2
  @1 = "llvm/test/Transforms/InstCombine/apint-add.ll":17:1 to 24:2
  @2 = "llvm/test/Transforms/InstCombine/apint-add.ll":27:1 to 34:2
  @3 = "llvm/test/Transforms/InstCombine/apint-add.ll":47:1 to 55:2
  @4 = "llvm/test/Transforms/InstCombine/apint-add.ll":48:1 to 50:35
  @5 = "llvm/test/Transforms/InstCombine/apint-add.ll":57:1 to 66:2
  @6 = "llvm/test/Transforms/InstCombine/apint-add.ll":58:1 to 60:32
  @7 = "llvm/test/Transforms/InstCombine/apint-add.ll":81:1 to 98:2
  @8 = "llvm/test/Transforms/InstCombine/apint-add.ll":82:1 to 89:32
  @9 = "llvm/test/Transforms/InstCombine/apint-add.ll":103:1 to 111:2
  @10 = "llvm/test/Transforms/InstCombine/apint-add.ll":114:1 to 122:2
  @11 = "llvm/test/Transforms/InstCombine/apint-add.ll":125:1 to 133:2
  @12 = "llvm/test/Transforms/InstCombine/apint-add.ll":136:1 to 146:2
  @13 = "llvm/test/Transforms/InstCombine/apint-add.ll":137:1 to 139:36
  @14 = "llvm/test/Transforms/InstCombine/apint-add.ll":149:1 to 158:2
  @15 = "llvm/test/Transforms/InstCombine/apint-add.ll":150:1 to 153:35
}
