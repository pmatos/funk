func @srem_sext_big_divisor(%x: i8) -> i32 {
^entry:
  %conv: i32 = sext %x @0
  %c: i32 = const 129 @0
  %r: i32 = srem %conv, %c @0
  ret %r @0
}

func @srem_sext_big_divisor.folded(%x: i8) -> i32 {
^entry:
  %conv: i32 = sext %x @1
  ret %conv @1
}

func @not_srem_sext_big_divisor(%x: i8) -> i32 {
^entry:
  %conv: i32 = sext %x @2
  %c: i32 = const 128 @2
  %r: i32 = srem %conv, %c @2
  ret %r @2
}

func @srem_zext_big_divisor(%x: i8) -> i32 {
^entry:
  %conv: i32 = zext %x @3
  %c: i32 = const 256 @3
  %r: i32 = srem %conv, %c @3
  ret %r @3
}

func @srem_zext_big_divisor.folded(%x: i8) -> i32 {
^entry:
  %conv: i32 = zext %x @4
  ret %conv @4
}

func @not_srem_zext_big_divisor(%x: i8) -> i32 {
^entry:
  %conv: i32 = zext %x @5
  %c: i32 = const 255 @5
  %r: i32 = srem %conv, %c @5
  ret %r @5
}

func @srem_dividend_known_smaller_than_pos_divisor_clear_bits(%x: i32) -> i32 {
^entry:
  %c: i32 = const 253 @6
  %and: i32 = and %x, %c @6
  %d: i32 = const 254 @6
  %r: i32 = srem %and, %d @6
  ret %r @6
}

func @srem_dividend_known_smaller_than_pos_divisor_clear_bits.folded(%x: i32) -> i32 {
^entry:
  %c: i32 = const 253 @7
  %and: i32 = and %x, %c @7
  ret %and @7
}

func @srem_dividend_known_smaller_than_neg_divisor_set_bits(%x: i32) -> i32 {
^entry:
  %c: i32 = const -253 @8
  %or: i32 = or %x, %c @8
  %d: i32 = const -254 @8
  %r: i32 = srem %or, %d @8
  ret %r @8
}

func @srem_dividend_known_smaller_than_neg_divisor_set_bits.folded(%x: i32) -> i32 {
^entry:
  %c: i32 = const -253 @9
  %or: i32 = or %x, %c @9
  ret %or @9
}

func @not_srem_dividend_known_smaller_than_neg_divisor_set_bits(%x: i32) -> i32 {
^entry:
  %c: i32 = const -253 @10
  %or: i32 = or %x, %c @10
  %d: i32 = const -253 @10
  %r: i32 = srem %or, %d @10
  ret %r @10
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":164:1 to 172:2
  @1 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":165:1 to 167:34
  @2 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":174:1 to 183:2
  @3 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":206:1 to 214:2
  @4 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":207:1 to 209:34
  @5 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":216:1 to 225:2
  @6 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":248:1 to 256:2
  @7 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":249:1 to 251:33
  @8 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":311:1 to 319:2
  @9 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":312:1 to 314:32
  @10 = "llvm/test/Transforms/InstSimplify/signed-div-rem.ll":321:1 to 330:2
}
