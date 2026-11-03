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

func @urem_dividend_known_smaller_than_constant_divisor2(%b: i1) -> i8 {
^entry:
  %t0: i8 = zext %b @11
  %c12: i8 = const 12 @11
  %xor: i8 = xor %t0, %c12 @11
  %c14: i8 = const 14 @11
  %r: i8 = urem %xor, %c14 @11
  ret %r @11
}

func @urem_constant_dividend_known_smaller_than_divisor(%x: i32) -> i32 {
^entry:
  %c251: i32 = const 251 @12
  %or: i32 = or %x, %c251 @12
  %c250: i32 = const 250 @12
  %r: i32 = urem %c250, %or @12
  ret %r @12
}

func @srem_with_sext_bool_divisor(%x: i1, %y: i32) -> i32 {
^entry:
  %s: i32 = sext %x @13
  %r: i32 = srem %y, %s @13
  ret %r @13
}

func @srem_minusone_divisor() -> i8 {
^entry:
  %min: i8 = const -128 @14
  %m1: i8 = const -1 @14
  %v: i8 = srem %min, %m1 @14
  ret %v @14
}

func @srem_of_mul_nsw(%x: i32, %y: i32) -> i32 {
^entry:
  %mul: i32 = mul nsw %x, %y @15
  %mod: i32 = srem %mul, %y @15
  ret %mod @15
}

func @srem_of_mul(%x: i32, %y: i32) -> i32 {
^entry:
  %mul: i32 = mul %x, %y @16
  %mod: i32 = srem %mul, %y @16
  ret %mod @16
}

func @urem_of_mul_nuw(%x: i32, %y: i32) -> i32 {
^entry:
  %mul: i32 = mul nuw %x, %y @17
  %mod: i32 = urem %mul, %y @17
  ret %mod @17
}

func @urem_of_mul_nsw(%x: i32, %y: i32) -> i32 {
^entry:
  %mul: i32 = mul nsw %x, %y @18
  %mod: i32 = urem %mul, %y @18
  ret %mod @18
}

func @srem_mul_udiv(%x: i8, %y: i8) -> i8 {
^entry:
  %d: i8 = udiv %x, %y @19
  %mul: i8 = mul %d, %y @19
  %mod: i8 = srem %mul, %y @19
  ret %mod @19
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
  @11 = "llvm/test/Transforms/InstSimplify/rem.ll":190:1 to 200:2
  @12 = "llvm/test/Transforms/InstSimplify/rem.ll":217:1 to 224:2
  @13 = "llvm/test/Transforms/InstSimplify/rem.ll":341:1 to 348:2
  @14 = "llvm/test/Transforms/InstSimplify/rem.ll":359:1 to 365:2
  @15 = "llvm/test/Transforms/InstSimplify/rem.ll":367:1 to 374:2
  @16 = "llvm/test/Transforms/InstSimplify/rem.ll":399:1 to 408:2
  @17 = "llvm/test/Transforms/InstSimplify/rem.ll":421:1 to 428:2
  @18 = "llvm/test/Transforms/InstSimplify/rem.ll":410:1 to 419:2
  @19 = "llvm/test/Transforms/InstSimplify/rem.ll":460:1 to 471:2
}
