func @zero_dividend(%A: i32) -> i32 {
^entry:
  %z: i32 = const 0 @0
  %B: i32 = urem %z, %A @0
  ret %B @0
}

func @zext_bool_srem_divisor(%x: i1, %y: i32) -> i32 {
^entry:
  %ext: i32 = zext %x @1
  %r: i32 = srem %y, %ext @1
  ret %r @1
}

func @select1(%x: i32, %b: i1) -> i32 {
^entry:
  %c1: i32 = const 1 @2
  %rhs: i32 = select %b, %x, %c1 @2
  %rem: i32 = srem %x, %rhs @2
  ret %rem @2
}

func @select2(%x: i32, %b: i1) -> i32 {
^entry:
  %c1: i32 = const 1 @3
  %rhs: i32 = select %b, %x, %c1 @3
  %rem: i32 = urem %x, %rhs @3
  ret %rem @3
}

func @rem1(%x: i32, %n: i32) -> i32 {
^entry:
  %mod: i32 = srem %x, %n @4
  %mod1: i32 = srem %mod, %n @4
  ret %mod1 @4
}

func @rem1.folded(%x: i32, %n: i32) -> i32 {
^entry:
  %mod: i32 = srem %x, %n @5
  ret %mod @5
}

func @rem2(%x: i32, %n: i32) -> i32 {
^entry:
  %mod: i32 = urem %x, %n @6
  %mod1: i32 = urem %mod, %n @6
  ret %mod1 @6
}

func @rem2.folded(%x: i32, %n: i32) -> i32 {
^entry:
  %mod: i32 = urem %x, %n @7
  ret %mod @7
}

func @rem3(%x: i32, %n: i32) -> i32 {
^entry:
  %mod: i32 = srem %x, %n @8
  %mod1: i32 = urem %mod, %n @8
  ret %mod1 @8
}

func @urem_dividend_known_smaller_than_constant_divisor(%x: i32) -> i32 {
^entry:
  %c250: i32 = const 250 @9
  %and: i32 = and %x, %c250 @9
  %c251: i32 = const 251 @9
  %r: i32 = urem %and, %c251 @9
  ret %r @9
}

func @urem_dividend_known_smaller_than_constant_divisor.folded(%x: i32) -> i32 {
^entry:
  %c250: i32 = const 250 @10
  %and: i32 = and %x, %c250 @10
  ret %and @10
}

func @not_urem_dividend_known_smaller_than_constant_divisor(%x: i32) -> i32 {
^entry:
  %c251: i32 = const 251 @11
  %and: i32 = and %x, %c251 @11
  %r: i32 = urem %and, %c251 @11
  ret %r @11
}

func @urem_dividend_known_smaller_than_constant_divisor2(%b: i1) -> i8 {
^entry:
  %t0: i8 = zext %b @12
  %c12: i8 = const 12 @12
  %xor: i8 = xor %t0, %c12 @12
  %c14: i8 = const 14 @12
  %r: i8 = urem %xor, %c14 @12
  ret %r @12
}

func @urem_dividend_known_smaller_than_constant_divisor2.folded(%b: i1) -> i8 {
^entry:
  %t0: i8 = zext %b @13
  %c12: i8 = const 12 @13
  %xor: i8 = xor %t0, %c12 @13
  ret %xor @13
}

func @not_urem_dividend_known_smaller_than_constant_divisor2(%b: i1) -> i8 {
^entry:
  %t0: i8 = zext %b @14
  %c12: i8 = const 12 @14
  %xor: i8 = xor %t0, %c12 @14
  %c13: i8 = const 13 @14
  %r: i8 = urem %xor, %c13 @14
  ret %r @14
}

func @urem_constant_dividend_known_smaller_than_divisor(%x: i32) -> i32 {
^entry:
  %c251: i32 = const 251 @15
  %or: i32 = or %x, %c251 @15
  %c250: i32 = const 250 @15
  %r: i32 = urem %c250, %or @15
  ret %r @15
}

func @not_urem_constant_dividend_known_smaller_than_divisor(%x: i32) -> i32 {
^entry:
  %c251: i32 = const 251 @16
  %or: i32 = or %x, %c251 @16
  %r: i32 = urem %c251, %or @16
  ret %r @16
}

func @urem_dividend_known_smaller_than_divisor(%x: i32, %y: i32) -> i32 {
^entry:
  %c250: i32 = const 250 @17
  %and: i32 = and %x, %c250 @17
  %c251: i32 = const 251 @17
  %or: i32 = or %y, %c251 @17
  %r: i32 = urem %and, %or @17
  ret %r @17
}

func @not_urem_dividend_known_smaller_than_divisor(%x: i32, %y: i32) -> i32 {
^entry:
  %c251: i32 = const 251 @18
  %and: i32 = and %x, %c251 @18
  %or: i32 = or %y, %c251 @18
  %r: i32 = urem %and, %or @18
  ret %r @18
}

func @rem7(%x: i32, %y: i32) -> i32 {
^entry:
  %shl: i32 = shl %x, %y @19
  %mod: i32 = srem %shl, %x @19
  ret %mod @19
}

func @rem10(%x: i32, %y: i32) -> i32 {
^entry:
  %shl: i32 = shl %x, %y @20
  %mod: i32 = urem %shl, %x @20
  ret %mod @20
}

func @srem_with_sext_bool_divisor(%x: i1, %y: i32) -> i32 {
^entry:
  %s: i32 = sext %x @21
  %r: i32 = srem %y, %s @21
  ret %r @21
}

func @srem_minusone_divisor() -> i8 {
^entry:
  %min: i8 = const -128 @22
  %m1: i8 = const -1 @22
  %v: i8 = srem %min, %m1 @22
  ret %v @22
}

func @srem_of_mul_nsw(%x: i32, %y: i32) -> i32 {
^entry:
  %mul: i32 = mul nsw %x, %y @23
  %mod: i32 = srem %mul, %y @23
  ret %mod @23
}

func @srem_of_mul(%x: i32, %y: i32) -> i32 {
^entry:
  %mul: i32 = mul %x, %y @24
  %mod: i32 = srem %mul, %y @24
  ret %mod @24
}

func @srem_of_mul_nuw(%x: i32, %y: i32) -> i32 {
^entry:
  %mul: i32 = mul nuw %x, %y @25
  %mod: i32 = srem %mul, %y @25
  ret %mod @25
}

func @urem_of_mul_nuw(%x: i32, %y: i32) -> i32 {
^entry:
  %mul: i32 = mul nuw %x, %y @26
  %mod: i32 = urem %mul, %y @26
  ret %mod @26
}

func @urem_of_mul_nsw(%x: i32, %y: i32) -> i32 {
^entry:
  %mul: i32 = mul nsw %x, %y @27
  %mod: i32 = urem %mul, %y @27
  ret %mod @27
}

func @urem_of_mul(%x: i32, %y: i32) -> i32 {
^entry:
  %mul: i32 = mul %x, %y @28
  %mod: i32 = urem %mul, %y @28
  ret %mod @28
}

func @srem_mul_udiv(%x: i8, %y: i8) -> i8 {
^entry:
  %d: i8 = udiv %x, %y @29
  %mul: i8 = mul %d, %y @29
  %mod: i8 = srem %mul, %y @29
  ret %mod @29
}

func @urem_mul_sdiv(%x: i8, %y: i8) -> i8 {
^entry:
  %d: i8 = sdiv %x, %y @30
  %mul: i8 = mul %y, %d @30
  %mod: i8 = urem %mul, %y @30
  ret %mod @30
}

func @simplify_urem_of_mul(%x: i8) -> i8 {
^entry:
  %c30: i8 = const 30 @31
  %mul: i8 = mul nuw %x, %c30 @31
  %c10: i8 = const 10 @31
  %r: i8 = urem %mul, %c10 @31
  ret %r @31
}

func @simplify_urem_of_mul_fail_bad_flag(%x: i8) -> i8 {
^entry:
  %c30: i8 = const 30 @32
  %mul: i8 = mul nsw %x, %c30 @32
  %c10: i8 = const 10 @32
  %r: i8 = urem %mul, %c10 @32
  ret %r @32
}

func @simplify_urem_of_mul_fail_bad_mod(%x: i8) -> i8 {
^entry:
  %c31: i8 = const 31 @33
  %mul: i8 = mul nuw %x, %c31 @33
  %c10: i8 = const 10 @33
  %r: i8 = urem %mul, %c10 @33
  ret %r @33
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/rem.ll":4:1 to 10:2
  @1 = "llvm/test/Transforms/InstSimplify/rem.ll":111:1 to 118:2
  @2 = "llvm/test/Transforms/InstSimplify/rem.ll":120:1 to 127:2
  @3 = "llvm/test/Transforms/InstSimplify/rem.ll":129:1 to 136:2
  @4 = "llvm/test/Transforms/InstSimplify/rem.ll":138:1 to 146:2
  @5 = "llvm/test/Transforms/InstSimplify/rem.ll":139:1 to 141:33
  @6 = "llvm/test/Transforms/InstSimplify/rem.ll":148:1 to 156:2
  @7 = "llvm/test/Transforms/InstSimplify/rem.ll":149:1 to 151:33
  @8 = "llvm/test/Transforms/InstSimplify/rem.ll":158:1 to 167:2
  @9 = "llvm/test/Transforms/InstSimplify/rem.ll":169:1 to 177:2
  @10 = "llvm/test/Transforms/InstSimplify/rem.ll":170:1 to 172:33
  @11 = "llvm/test/Transforms/InstSimplify/rem.ll":179:1 to 188:2
  @12 = "llvm/test/Transforms/InstSimplify/rem.ll":190:1 to 200:2
  @13 = "llvm/test/Transforms/InstSimplify/rem.ll":191:1 to 194:32
  @14 = "llvm/test/Transforms/InstSimplify/rem.ll":204:1 to 215:2
  @15 = "llvm/test/Transforms/InstSimplify/rem.ll":217:1 to 224:2
  @16 = "llvm/test/Transforms/InstSimplify/rem.ll":226:1 to 235:2
  @17 = "llvm/test/Transforms/InstSimplify/rem.ll":239:1 to 250:2
  @18 = "llvm/test/Transforms/InstSimplify/rem.ll":252:1 to 263:2
  @19 = "llvm/test/Transforms/InstSimplify/rem.ll":299:1 to 308:2
  @20 = "llvm/test/Transforms/InstSimplify/rem.ll":330:1 to 339:2
  @21 = "llvm/test/Transforms/InstSimplify/rem.ll":341:1 to 348:2
  @22 = "llvm/test/Transforms/InstSimplify/rem.ll":359:1 to 365:2
  @23 = "llvm/test/Transforms/InstSimplify/rem.ll":367:1 to 374:2
  @24 = "llvm/test/Transforms/InstSimplify/rem.ll":399:1 to 408:2
  @25 = "llvm/test/Transforms/InstSimplify/rem.ll":388:1 to 397:2
  @26 = "llvm/test/Transforms/InstSimplify/rem.ll":421:1 to 428:2
  @27 = "llvm/test/Transforms/InstSimplify/rem.ll":410:1 to 419:2
  @28 = "llvm/test/Transforms/InstSimplify/rem.ll":439:1 to 448:2
  @29 = "llvm/test/Transforms/InstSimplify/rem.ll":460:1 to 471:2
  @30 = "llvm/test/Transforms/InstSimplify/rem.ll":483:1 to 494:2
  @31 = "llvm/test/Transforms/InstSimplify/rem.ll":516:1 to 523:2
  @32 = "llvm/test/Transforms/InstSimplify/rem.ll":525:1 to 534:2
  @33 = "llvm/test/Transforms/InstSimplify/rem.ll":536:1 to 545:2
}
