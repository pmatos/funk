func @tautological_ule(%x: i8) -> i1 {
^entry:
  %c: i8 = const -1 @0
  %cmp: i1 = icmp ule %x, %c @0
  ret %cmp @0
}

func @tautological_ugt(%x: i8) -> i1 {
^entry:
  %c: i8 = const -1 @1
  %cmp: i1 = icmp ugt %x, %c @1
  ret %cmp @1
}

func @urem3(%X: i32) -> i1 {
^entry:
  %c: i32 = const 10 @2
  %A: i32 = urem %X, %c @2
  %k: i32 = const 15 @2
  %B: i1 = icmp ult %A, %k @2
  ret %B @2
}

func @srem1(%X: i32) -> i1 {
^entry:
  %c: i32 = const -5 @3
  %A: i32 = srem %X, %c @3
  %k: i32 = const 5 @3
  %B: i1 = icmp sgt %A, %k @3
  ret %B @3
}

func @udiv5(%X: i32) -> i1 {
^entry:
  %c: i32 = const 123 @4
  %A: i32 = udiv %c, %X @4
  %k: i32 = const 124 @4
  %B: i1 = icmp ugt %A, %k @4
  ret %B @4
}

func @udiv1(%X: i32) -> i1 {
^entry:
  %c: i32 = const 1000000 @5
  %A: i32 = udiv %X, %c @5
  %k: i32 = const 5000 @5
  %B: i1 = icmp ult %A, %k @5
  ret %B @5
}

func @compare_dividend(%X: i32) -> i1 {
^entry:
  %c: i32 = const 2 @6
  %A: i32 = sdiv %c, %X @6
  %k: i32 = const 3 @6
  %B: i1 = icmp eq %A, %k @6
  ret %B @6
}

func @sdiv1(%X: i32) -> i1 {
^entry:
  %c: i32 = const 1000000 @7
  %A: i32 = sdiv %X, %c @7
  %k: i32 = const 3000 @7
  %B: i1 = icmp slt %A, %k @7
  ret %B @7
}

func @lshr2(%X: i32) -> i1 {
^entry:
  %c: i32 = const 30 @8
  %A: i32 = lshr %X, %c @8
  %k: i32 = const 8 @8
  %B: i1 = icmp ugt %A, %k @8
  ret %B @8
}

func @lshr_sgt_false(%X: i32) -> i1 {
^entry:
  %c: i32 = const 1 @9
  %A: i32 = lshr %c, %X @9
  %k: i32 = const 1 @9
  %B: i1 = icmp sgt %A, %k @9
  ret %B @9
}

func @ashr2(%X: i32) -> i1 {
^entry:
  %c: i32 = const 30 @10
  %A: i32 = ashr %X, %c @10
  %k: i32 = const -5 @10
  %B: i1 = icmp slt %A, %k @10
  ret %B @10
}

func @ashr_sgt_false(%X: i32) -> i1 {
^entry:
  %c: i32 = const -30 @11
  %A: i32 = ashr %c, %X @11
  %k: i32 = const -1 @11
  %B: i1 = icmp sgt %A, %k @11
  ret %B @11
}

func @or1(%X: i32) -> i1 {
^entry:
  %c: i32 = const 62 @12
  %A: i32 = or %X, %c @12
  %k: i32 = const 50 @12
  %B: i1 = icmp ult %A, %k @12
  ret %B @12
}

func @or4_true(%X: i8) -> i1 {
^entry:
  %c: i8 = const -64 @13
  %A: i8 = or %X, %c @13
  %k: i8 = const -64 @13
  %B: i1 = icmp sge %A, %k @13
  ret %B @13
}

func @or5_true(%X: i8) -> i1 {
^entry:
  %c: i8 = const -64 @14
  %A: i8 = or %X, %c @14
  %k: i8 = const -64 @14
  %B: i1 = icmp uge %A, %k @14
  ret %B @14
}

func @and1(%X: i32) -> i1 {
^entry:
  %c: i32 = const 62 @15
  %A: i32 = and %X, %c @15
  %k: i32 = const 70 @15
  %B: i1 = icmp ugt %A, %k @15
  ret %B @15
}

func @and2(%X: i32) -> i1 {
^entry:
  %c: i32 = const 62 @16
  %A: i32 = and %X, %c @16
  %k: i32 = const 70 @16
  %B: i1 = icmp sgt %A, %k @16
  ret %B @16
}

func @tautological9(%X: i32) -> i1 {
^entry:
  %c: i32 = const 13 @17
  %A: i32 = add nuw %X, %c @17
  %k: i32 = const 12 @17
  %B: i1 = icmp ne %A, %k @17
  ret %B @17
}

func @add_nsw_neg_const1(%X: i32) -> i1 {
^entry:
  %c: i32 = const -2147483647 @18
  %A: i32 = add nsw %X, %c @18
  %k: i32 = const 0 @18
  %B: i1 = icmp sgt %A, %k @18
  ret %B @18
}

func @add_nsw_sgt(%X: i8) -> i1 {
^entry:
  %c: i8 = const 5 @19
  %A: i8 = add nsw %X, %c @19
  %k: i8 = const -124 @19
  %B: i1 = icmp sgt %A, %k @19
  ret %B @19
}

func @add_nsw_nuw_sgt(%X: i8) -> i1 {
^entry:
  %c: i8 = const 5 @20
  %A: i8 = add nuw nsw %X, %c @20
  %k: i8 = const -124 @20
  %B: i1 = icmp sgt %A, %k @20
  ret %B @20
}

func @add_nsw_sgt_limit(%X: i8) -> i1 {
^entry:
  %c: i8 = const 4 @21
  %A: i8 = add nsw %X, %c @21
  %k: i8 = const -124 @21
  %B: i1 = icmp sgt %A, %k @21
  ret %B @21
}

func @add_nsw_slt(%X: i8) -> i1 {
^entry:
  %c: i8 = const 5 @22
  %A: i8 = add nsw %X, %c @22
  %k: i8 = const -123 @22
  %B: i1 = icmp slt %A, %k @22
  ret %B @22
}

func @add_nsw_slt_limit(%X: i8) -> i1 {
^entry:
  %c: i8 = const 5 @23
  %A: i8 = add nsw %X, %c @23
  %k: i8 = const -122 @23
  %B: i1 = icmp slt %A, %k @23
  ret %B @23
}

func @add_nsw_pos_const5(%X: i32) -> i1 {
^entry:
  %c: i32 = const 42 @24
  %A: i32 = add nsw %X, %c @24
  %k: i32 = const -2147483607 @24
  %B: i1 = icmp eq %A, %k @24
  ret %B @24
}

func @mul_nuw_urem_cmp_constant1(%X: i8) -> i1 {
^entry:
  %c: i8 = const 43 @25
  %A: i8 = mul nuw %X, %c @25
  %k: i8 = const 42 @25
  %B: i1 = icmp eq %A, %k @25
  ret %B @25
}

func @mul_urem_cmp_constant1(%X: i8) -> i1 {
^entry:
  %c: i8 = const 43 @26
  %A: i8 = mul %X, %c @26
  %k: i8 = const 42 @26
  %B: i1 = icmp eq %A, %k @26
  ret %B @26
}

func @mul_nsw_srem_cmp_constant1(%X: i8) -> i1 {
^entry:
  %c: i8 = const 43 @27
  %A: i8 = mul nsw %X, %c @27
  %k: i8 = const 45 @27
  %B: i1 = icmp eq %A, %k @27
  ret %B @27
}

func @mul_nsw_by_zero(%x: i8) -> i1 {
^bb1:
  br ^bb3 @28
^bb2:
  %c45: i8 = const 45 @28
  %r: i1 = icmp eq %m, %c45 @28
  ret %r @28
^bb3:
  %zero: i8 = const 0 @28
  %m: i8 = mul nsw %x, %zero @28
  br ^bb2 @28
}

func @mul_nuw_by_zero(%x: i8) -> i1 {
^bb1:
  br ^bb3 @29
^bb2:
  %c45: i8 = const 45 @29
  %r: i1 = icmp eq %m, %c45 @29
  ret %r @29
^bb3:
  %zero: i8 = const 0 @29
  %m: i8 = mul nuw %x, %zero @29
  br ^bb2 @29
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":6:1 to 12:2
  @1 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":30:1 to 36:2
  @2 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":55:1 to 62:2
  @3 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":83:1 to 90:2
  @4 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":111:1 to 118:2
  @5 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":130:1 to 137:2
  @6 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":149:1 to 156:2
  @7 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":169:1 to 176:2
  @8 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":292:1 to 299:2
  @9 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":330:1 to 337:2
  @10 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":349:1 to 356:2
  @11 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":368:1 to 375:2
  @12 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":406:1 to 413:2
  @13 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":481:1 to 488:2
  @14 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":502:1 to 509:2
  @15 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":523:1 to 530:2
  @16 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":542:1 to 549:2
  @17 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":597:1 to 604:2
  @18 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":617:1 to 624:2
  @19 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":626:1 to 633:2
  @20 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":637:1 to 644:2
  @21 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":648:1 to 657:2
  @22 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":659:1 to 666:2
  @23 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":681:1 to 690:2
  @24 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":803:1 to 810:2
  @25 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":881:1 to 888:2
  @26 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":936:1 to 945:2
  @27 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":988:1 to 995:2
  @28 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":1095:1 to 1112:2
  @29 = "llvm/test/Transforms/InstSimplify/icmp-constant.ll":1116:1 to 1133:2
}
