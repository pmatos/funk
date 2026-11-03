func @zero_dividend(%A: i32) -> i32 {
^entry:
  %z: i32 = const 0 @0
  %B: i32 = sdiv %z, %A @0
  ret %B @0
}

func @zext_bool_udiv_divisor(%x: i1, %y: i32) -> i32 {
^entry:
  %ext: i32 = zext %x @1
  %r: i32 = udiv %y, %ext @1
  ret %r @1
}

func @udiv_dividend_known_smaller_than_constant_divisor(%x: i32) -> i32 {
^entry:
  %c250: i32 = const 250 @2
  %and: i32 = and %x, %c250 @2
  %c251: i32 = const 251 @2
  %div: i32 = udiv %and, %c251 @2
  ret %div @2
}

func @not_udiv_dividend_known_smaller_than_constant_divisor(%x: i32) -> i32 {
^entry:
  %c251: i32 = const 251 @3
  %and: i32 = and %x, %c251 @3
  %div: i32 = udiv %and, %c251 @3
  ret %div @3
}

func @udiv_constant_dividend_known_smaller_than_divisor(%x: i32) -> i32 {
^entry:
  %c251: i32 = const 251 @4
  %or: i32 = or %x, %c251 @4
  %c250: i32 = const 250 @4
  %div: i32 = udiv %c250, %or @4
  ret %div @4
}

func @not_udiv_constant_dividend_known_smaller_than_divisor(%x: i32) -> i32 {
^entry:
  %c251: i32 = const 251 @5
  %or: i32 = or %x, %c251 @5
  %div: i32 = udiv %c251, %or @5
  ret %div @5
}

func @udiv_dividend_known_smaller_than_constant_divisor2(%b: i1) -> i8 {
^entry:
  %t0: i8 = zext %b @6
  %c12: i8 = const 12 @6
  %xor: i8 = xor %t0, %c12 @6
  %c14: i8 = const 14 @6
  %r: i8 = udiv %xor, %c14 @6
  ret %r @6
}

func @not_udiv_dividend_known_smaller_than_constant_divisor2(%b: i1) -> i8 {
^entry:
  %t0: i8 = zext %b @7
  %c12: i8 = const 12 @7
  %xor: i8 = xor %t0, %c12 @7
  %c13: i8 = const 13 @7
  %r: i8 = udiv %xor, %c13 @7
  ret %r @7
}

func @sdiv_minusone_divisor() -> i8 {
^entry:
  %min: i8 = const -128 @8
  %m1: i8 = const -1 @8
  %v: i8 = sdiv %min, %m1 @8
  ret %v @8
}

func @const_sdiv_zero_negone() -> i64 {
^entry:
  %z: i64 = const 0 @9
  %m1: i64 = const -1 @9
  %div: i64 = sdiv %z, %m1 @9
  ret %div @9
}

func @sdiv_exact_trailing_zeros(%x: i8) -> i8 {
^entry:
  %c1: i8 = const 1 @10
  %o: i8 = or %x, %c1 @10
  %c: i8 = const -42 @10
  %r: i8 = sdiv exact %o, %c @10
  ret %r @10
}

func @sdiv_exact_trailing_zeros_eq(%x: i8) -> i8 {
^entry:
  %c2: i8 = const 2 @11
  %o: i8 = or %x, %c2 @11
  %c: i8 = const -42 @11
  %r: i8 = sdiv exact %o, %c @11
  ret %r @11
}

func @sdiv_one_srem_divisor(%a: i32, %b: i32) -> i32 {
^entry:
  %c1: i32 = const 1 @12
  %srem: i32 = srem %c1, %b @12
  %r: i32 = sdiv %a, %srem @12
  ret %r @12
}

func @sdiv_one_urem_divisor(%a: i32, %b: i32) -> i32 {
^entry:
  %c1: i32 = const 1 @13
  %urem: i32 = urem %c1, %b @13
  %r: i32 = sdiv %a, %urem @13
  ret %r @13
}

func @udiv_one_srem_divisor(%a: i32, %b: i32) -> i32 {
^entry:
  %c1: i32 = const 1 @14
  %srem: i32 = srem %c1, %b @14
  %r: i32 = udiv %a, %srem @14
  ret %r @14
}

func @udiv_one_urem_divisor(%a: i32, %b: i32) -> i32 {
^entry:
  %c1: i32 = const 1 @15
  %urem: i32 = urem %c1, %b @15
  %r: i32 = udiv %a, %urem @15
  ret %r @15
}

func @srem_one_srem_divisor(%a: i32, %b: i32) -> i32 {
^entry:
  %c1: i32 = const 1 @16
  %srem: i32 = srem %c1, %b @16
  %r: i32 = srem %a, %srem @16
  ret %r @16
}

func @urem_one_srem_divisor(%a: i32, %b: i32) -> i32 {
^entry:
  %c1: i32 = const 1 @17
  %srem: i32 = srem %c1, %b @17
  %r: i32 = urem %a, %srem @17
  ret %r @17
}

func @srem_one_urem_divisor(%a: i32, %b: i32) -> i32 {
^entry:
  %c1: i32 = const 1 @18
  %urem: i32 = urem %c1, %b @18
  %r: i32 = srem %a, %urem @18
  ret %r @18
}

func @urem_one_urem_divisor(%a: i32, %b: i32) -> i32 {
^entry:
  %c1: i32 = const 1 @19
  %urem: i32 = urem %c1, %b @19
  %r: i32 = urem %a, %urem @19
  ret %r @19
}

func @sdiv_and_one_divisor(%x: i32, %y: i32) -> i32 {
^entry:
  %c1: i32 = const 1 @20
  %and: i32 = and %x, %c1 @20
  %res: i32 = sdiv %y, %and @20
  ret %res @20
}

func @sdiv_neg_or_divisor(%x: i32, %y: i32) -> i32 {
^entry:
  %c: i32 = const -2 @21
  %or: i32 = or %x, %c @21
  %m1: i32 = const -1 @21
  %neg: i32 = xor %or, %m1 @21
  %res: i32 = sdiv %y, %neg @21
  ret %res @21
}

func @sdiv_neg_or_multi_one_bit_divisor(%x: i32, %y: i32) -> i32 {
^entry:
  %c: i32 = const -3 @22
  %or: i32 = or %x, %c @22
  %m1: i32 = const -1 @22
  %neg: i32 = xor %or, %m1 @22
  %res: i32 = sdiv %y, %neg @22
  ret %res @22
}

func @udiv_exact_mul_nsw(%x: i8) -> i8 {
^entry:
  %c: i8 = const 24 @23
  %a: i8 = mul nsw %x, %c @23
  %b: i8 = udiv exact %a, %c @23
  ret %b @23
}

func @sdiv_exact_mul_nuw(%x: i8) -> i8 {
^entry:
  %c: i8 = const 24 @24
  %a: i8 = mul nuw %x, %c @24
  %b: i8 = sdiv exact %a, %c @24
  ret %b @24
}

func @udiv_exact_mul(%x: i8) -> i8 {
^entry:
  %c: i8 = const 24 @25
  %a: i8 = mul %x, %c @25
  %b: i8 = udiv exact %a, %c @25
  ret %b @25
}

func @udiv_mul_nsw(%x: i8) -> i8 {
^entry:
  %c: i8 = const 24 @26
  %a: i8 = mul nsw %x, %c @26
  %b: i8 = udiv %a, %c @26
  ret %b @26
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/div.ll":4:1 to 10:2
  @1 = "llvm/test/Transforms/InstSimplify/div.ll":102:1 to 109:2
  @2 = "llvm/test/Transforms/InstSimplify/div.ll":120:1 to 127:2
  @3 = "llvm/test/Transforms/InstSimplify/div.ll":129:1 to 138:2
  @4 = "llvm/test/Transforms/InstSimplify/div.ll":140:1 to 147:2
  @5 = "llvm/test/Transforms/InstSimplify/div.ll":149:1 to 158:2
  @6 = "llvm/test/Transforms/InstSimplify/div.ll":160:1 to 168:2
  @7 = "llvm/test/Transforms/InstSimplify/div.ll":172:1 to 183:2
  @8 = "llvm/test/Transforms/InstSimplify/div.ll":225:1 to 231:2
  @9 = "llvm/test/Transforms/InstSimplify/div.ll":300:1 to 306:2
  @10 = "llvm/test/Transforms/InstSimplify/div.ll":342:1 to 349:2
  @11 = "llvm/test/Transforms/InstSimplify/div.ll":353:1 to 362:2
  @12 = "llvm/test/Transforms/InstSimplify/div.ll":442:1 to 449:2
  @13 = "llvm/test/Transforms/InstSimplify/div.ll":451:1 to 458:2
  @14 = "llvm/test/Transforms/InstSimplify/div.ll":460:1 to 467:2
  @15 = "llvm/test/Transforms/InstSimplify/div.ll":469:1 to 476:2
  @16 = "llvm/test/Transforms/InstSimplify/div.ll":478:1 to 485:2
  @17 = "llvm/test/Transforms/InstSimplify/div.ll":487:1 to 494:2
  @18 = "llvm/test/Transforms/InstSimplify/div.ll":496:1 to 503:2
  @19 = "llvm/test/Transforms/InstSimplify/div.ll":505:1 to 512:2
  @20 = "llvm/test/Transforms/InstSimplify/div.ll":523:1 to 530:2
  @21 = "llvm/test/Transforms/InstSimplify/div.ll":541:1 to 549:2
  @22 = "llvm/test/Transforms/InstSimplify/div.ll":551:1 to 562:2
  @23 = "llvm/test/Transforms/InstSimplify/div.ll":575:1 to 582:2
  @24 = "llvm/test/Transforms/InstSimplify/div.ll":584:1 to 591:2
  @25 = "llvm/test/Transforms/InstSimplify/div.ll":628:1 to 637:2
  @26 = "llvm/test/Transforms/InstSimplify/div.ll":650:1 to 659:2
}
