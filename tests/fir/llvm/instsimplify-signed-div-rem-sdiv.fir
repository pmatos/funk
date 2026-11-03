func @sdiv_sext_big_divisor(%x: i8) -> i32 {
^entry:
  %conv: i32 = sext %x @0
  %c: i32 = const 129 @0
  %r: i32 = sdiv %conv, %c @0
  ret %r @0
}

func @not_sdiv_sext_big_divisor(%x: i8) -> i32 {
^entry:
  %conv: i32 = sext %x @1
  %c: i32 = const 128 @1
  %r: i32 = sdiv %conv, %c @1
  ret %r @1
}

func @sdiv_sext_small_divisor(%x: i8) -> i32 {
^entry:
  %conv: i32 = sext %x @2
  %c: i32 = const -129 @2
  %r: i32 = sdiv %conv, %c @2
  ret %r @2
}

func @not_sdiv_sext_small_divisor(%x: i8) -> i32 {
^entry:
  %conv: i32 = sext %x @3
  %c: i32 = const -128 @3
  %r: i32 = sdiv %conv, %c @3
  ret %r @3
}

func @sdiv_zext_big_divisor(%x: i8) -> i32 {
^entry:
  %conv: i32 = zext %x @4
  %c: i32 = const 256 @4
  %r: i32 = sdiv %conv, %c @4
  ret %r @4
}

func @not_sdiv_zext_big_divisor(%x: i8) -> i32 {
^entry:
  %conv: i32 = zext %x @5
  %c: i32 = const 255 @5
  %r: i32 = sdiv %conv, %c @5
  ret %r @5
}

func @sdiv_zext_small_divisor(%x: i8) -> i32 {
^entry:
  %conv: i32 = zext %x @6
  %c: i32 = const -256 @6
  %r: i32 = sdiv %conv, %c @6
  ret %r @6
}

func @not_sdiv_zext_small_divisor(%x: i8) -> i32 {
^entry:
  %conv: i32 = zext %x @7
  %c: i32 = const -255 @7
  %r: i32 = sdiv %conv, %c @7
  ret %r @7
}

func @sdiv_dividend_known_smaller_than_pos_divisor_clear_bits(%x: i32) -> i32 {
^entry:
  %c: i32 = const 253 @8
  %and: i32 = and %x, %c @8
  %d: i32 = const 254 @8
  %r: i32 = sdiv %and, %d @8
  ret %r @8
}

func @not_sdiv_dividend_known_smaller_than_pos_divisor_clear_bits(%x: i32) -> i32 {
^entry:
  %c: i32 = const 253 @9
  %and: i32 = and %x, %c @9
  %d: i32 = const 253 @9
  %r: i32 = sdiv %and, %d @9
  ret %r @9
}

func @sdiv_dividend_known_smaller_than_neg_divisor_clear_bits(%x: i32) -> i32 {
^entry:
  %c: i32 = const 253 @10
  %and: i32 = and %x, %c @10
  %d: i32 = const -254 @10
  %r: i32 = sdiv %and, %d @10
  ret %r @10
}

func @sdiv_dividend_known_smaller_than_pos_divisor_set_bits(%x: i32) -> i32 {
^entry:
  %c: i32 = const -253 @11
  %or: i32 = or %x, %c @11
  %d: i32 = const 254 @11
  %r: i32 = sdiv %or, %d @11
  ret %r @11
}

func @not_sdiv_dividend_known_smaller_than_pos_divisor_set_bits(%x: i32) -> i32 {
^entry:
  %c: i32 = const -253 @12
  %or: i32 = or %x, %c @12
  %d: i32 = const 253 @12
  %r: i32 = sdiv %or, %d @12
  ret %r @12
}

func @sdiv_dividend_known_smaller_than_neg_divisor_set_bits(%x: i32) -> i32 {
^entry:
  %c: i32 = const -253 @13
  %or: i32 = or %x, %c @13
  %d: i32 = const -254 @13
  %r: i32 = sdiv %or, %d @13
  ret %r @13
}

func @sdiv_min_dividend(%x: i8) -> i16 {
^entry:
  %z: i16 = zext %x @14
  %c: i16 = const -32768 @14
  %d: i16 = sdiv %c, %z @14
  ret %d @14
}

func @sdiv_min_divisor(%x: i8) -> i16 {
^entry:
  %z: i16 = zext %x @15
  %c: i16 = const -32768 @15
  %d: i16 = sdiv %z, %c @15
  ret %d @15
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":4:1 to 11:2
  @1 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":13:1 to 22:2
  @2 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":24:1 to 31:2
  @3 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":33:1 to 42:2
  @4 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":44:1 to 51:2
  @5 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":53:1 to 62:2
  @6 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":64:1 to 71:2
  @7 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":73:1 to 82:2
  @8 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":84:1 to 91:2
  @9 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":93:1 to 102:2
  @10 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":104:1 to 111:2
  @11 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":124:1 to 131:2
  @12 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":133:1 to 142:2
  @13 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":144:1 to 151:2
  @14 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":334:1 to 343:2
  @15 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":347:1 to 354:2
}
