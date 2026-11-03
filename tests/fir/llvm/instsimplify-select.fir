func @bool_true_or_false(%cond: i1) -> i1 {
^entry:
  %t: i1 = const true @0
  %f: i1 = const false @0
  %s: i1 = select %cond, %t, %f @0
  ret %s @0
}

func @cond_is_false(%A: i32, %B: i32) -> i32 {
^entry:
  %f: i1 = const false @1
  %C: i32 = select %f, %A, %B @1
  ret %C @1
}

func @cond_is_true(%A: i32, %B: i32) -> i32 {
^entry:
  %t: i1 = const true @2
  %C: i32 = select %t, %A, %B @2
  ret %C @2
}

func @equal_arms(%cond: i1, %x: i32) -> i32 {
^entry:
  %V: i32 = select %cond, %x, %x @3
  ret %V @3
}

func @test1(%x: i32) -> i32 {
^entry:
  %one: i32 = const 1 @4
  %and: i32 = and %x, %one @4
  %zero: i32 = const 0 @4
  %cmp: i1 = icmp eq %and, %zero @4
  %m2: i32 = const -2 @4
  %and1: i32 = and %x, %m2 @4
  %and1.x: i32 = select %cmp, %and1, %x @4
  ret %and1.x @4
}

func @test3(%x: i32) -> i32 {
^entry:
  %one: i32 = const 1 @5
  %and: i32 = and %x, %one @5
  %zero: i32 = const 0 @5
  %cmp: i1 = icmp ne %and, %zero @5
  %m2: i32 = const -2 @5
  %and1: i32 = and %x, %m2 @5
  %and1.x: i32 = select %cmp, %and1, %x @5
  ret %and1.x @5
}

func @test4(%X: i32) -> i32 {
^entry:
  %k: i32 = const 0 @6
  %cmp: i1 = icmp slt %X, %k @6
  %c: i32 = const -2147483648 @6
  %or: i32 = or %X, %c @6
  %cond: i32 = select %cmp, %X, %or @6
  ret %cond @6
}

func @test4.folded(%X: i32) -> i32 {
^entry:
  %c: i32 = const -2147483648 @7
  %or: i32 = or %X, %c @7
  ret %or @7
}

func @test6(%X: i32) -> i32 {
^entry:
  %k: i32 = const 0 @8
  %cmp: i1 = icmp slt %X, %k @8
  %c: i32 = const 2147483647 @8
  %and: i32 = and %X, %c @8
  %cond: i32 = select %cmp, %and, %X @8
  ret %cond @8
}

func @test6.folded(%X: i32) -> i32 {
^entry:
  %c: i32 = const 2147483647 @9
  %and: i32 = and %X, %c @9
  ret %and @9
}

func @test12(%X: i32) -> i32 {
^entry:
  %k: i32 = const 4 @10
  %cmp: i1 = icmp ult %X, %k @10
  %c: i32 = const 3 @10
  %and: i32 = and %X, %c @10
  %cond: i32 = select %cmp, %X, %and @10
  ret %cond @10
}

func @test12.folded(%X: i32) -> i32 {
^entry:
  %c: i32 = const 3 @11
  %and: i32 = and %X, %c @11
  ret %and @11
}

func @test13(%X: i32) -> i32 {
^entry:
  %k: i32 = const 3 @12
  %cmp: i1 = icmp ugt %X, %k @12
  %c: i32 = const 3 @12
  %and: i32 = and %X, %c @12
  %cond: i32 = select %cmp, %and, %X @12
  ret %cond @12
}

func @select_icmp_and_8_eq_0_or_8(%x: i32) -> i32 {
^entry:
  %c8: i32 = const 8 @13
  %and: i32 = and %x, %c8 @13
  %zero: i32 = const 0 @13
  %cmp: i1 = icmp eq %and, %zero @13
  %or: i32 = or %x, %c8 @13
  %sel: i32 = select %cmp, %or, %x @13
  ret %sel @13
}

func @select_icmp_and_8_eq_0_or_8.folded(%x: i32) -> i32 {
^entry:
  %c8: i32 = const 8 @14
  %or: i32 = or %x, %c8 @14
  ret %or @14
}

func @select_icmp_trunc_8_ne_0_or_128(%x: i32) -> i32 {
^entry:
  %trunc: i8 = trunc %x @15
  %m1: i8 = const -1 @15
  %cmp: i1 = icmp sgt %trunc, %m1 @15
  %c128: i32 = const 128 @15
  %or: i32 = or %x, %c128 @15
  %sel: i32 = select %cmp, %or, %x @15
  ret %sel @15
}

func @select_neutral_add_rhs(%x: i32, %y: i32) -> i32 {
^entry:
  %zero: i32 = const 0 @16
  %cmp: i1 = icmp ne %y, %zero @16
  %add: i32 = add %x, %y @16
  %sel: i32 = select %cmp, %add, %x @16
  ret %sel @16
}

func @select_neutral_add_rhs.folded(%x: i32, %y: i32) -> i32 {
^entry:
  %add: i32 = add %x, %y @17
  ret %add @17
}

func @select_neutral_sub_lhs(%x: i32, %y: i32) -> i32 {
^entry:
  %zero: i32 = const 0 @18
  %cmp: i1 = icmp ne %y, %zero @18
  %add: i32 = sub %y, %x @18
  %sel: i32 = select %cmp, %add, %x @18
  ret %sel @18
}

func @select_eq_xor_recursive(%a: i8, %b: i8) -> i8 {
^entry:
  %xor: i8 = xor %a, %b @19
  %m1: i8 = const -1 @19
  %inv: i8 = xor %xor, %m1 @19
  %cmp: i1 = icmp eq %a, %b @19
  %sel: i8 = select %cmp, %m1, %inv @19
  ret %sel @19
}

func @select_eq_xor_recursive.folded(%a: i8, %b: i8) -> i8 {
^entry:
  %xor: i8 = xor %a, %b @20
  %m1: i8 = const -1 @20
  %inv: i8 = xor %xor, %m1 @20
  ret %inv @20
}

func @select_eq_and_recursive(%a: i8) -> i8 {
^entry:
  %zero: i8 = const 0 @21
  %neg: i8 = sub %zero, %a @21
  %and: i8 = and %neg, %a @21
  %one: i8 = const 1 @21
  %add: i8 = add %and, %one @21
  %cmp: i1 = icmp eq %a, %zero @21
  %sel: i8 = select %cmp, %one, %add @21
  ret %sel @21
}

func @select_eq_xor_recursive_allow_refinement(%a: i8, %b: i8) -> i8 {
^entry:
  %xor1: i8 = add %a, %b @22
  %xor2: i8 = xor %a, %xor1 @22
  %zero: i8 = const 0 @22
  %cmp: i1 = icmp eq %b, %zero @22
  %sel: i8 = select %cmp, %xor2, %zero @22
  ret %sel @22
}

func @poison2(%cond: i1, %x: i32) -> i32 {
^entry:
  %n: i32 = const 32 @23
  %p: i32 = shl %n, %n @23
  %v: i32 = select %cond, %p, %x @23
  ret %v @23
}

func @poison3(%cond: i1, %x: i32) -> i32 {
^entry:
  %n: i32 = const 32 @24
  %p: i32 = shl %n, %n @24
  %v: i32 = select %cond, %x, %p @24
  ret %v @24
}

func @replace_false_op_eq_neg_and(%x: i8) -> i8 {
^entry:
  %zero: i8 = const 0 @25
  %eq0: i1 = icmp eq %x, %zero @25
  %neg: i8 = sub %zero, %x @25
  %and: i8 = and %neg, %x @25
  %sel: i8 = select %eq0, %zero, %and @25
  ret %sel @25
}

func @replace_false_op_eq_shl_or(%x: i8) -> i8 {
^entry:
  %m1: i8 = const -1 @26
  %eq0: i1 = icmp eq %x, %m1 @26
  %c3: i8 = const 3 @26
  %shl: i8 = shl %x, %c3 @26
  %or: i8 = or %x, %shl @26
  %sel: i8 = select %eq0, %m1, %or @26
  ret %sel @26
}

func @replace_false_op_sgt_neg_and(%x: i8) -> i8 {
^entry:
  %zero: i8 = const 0 @27
  %eq0: i1 = icmp sgt %x, %zero @27
  %neg: i8 = sub %zero, %x @27
  %and: i8 = and %neg, %x @27
  %sel: i8 = select %eq0, %zero, %and @27
  ret %sel @27
}

func @select_sub_cmp(%0: i8, %1: i8) -> i8 {
^entry:
  %3: i1 = icmp eq %1, %0 @28
  %4: i8 = sub nsw %1, %0 @28
  %z: i8 = const 0 @28
  %5: i8 = select %3, %z, %4 @28
  ret %5 @28
}

func @select_sub_cmp.folded(%0: i8, %1: i8) -> i8 {
^entry:
  %4: i8 = sub nsw %1, %0 @29
  ret %4 @29
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/select.ll":4:1 to 10:2
  @1 = "llvm/test/Transforms/InstSimplify/select.ll":36:1 to 42:2
  @2 = "llvm/test/Transforms/InstSimplify/select.ll":44:1 to 50:2
  @3 = "llvm/test/Transforms/InstSimplify/select.ll":52:1 to 58:2
  @4 = "llvm/test/Transforms/InstSimplify/select.ll":132:1 to 141:2
  @5 = "llvm/test/Transforms/InstSimplify/select.ll":154:1 to 164:2
  @6 = "llvm/test/Transforms/InstSimplify/select.ll":166:1 to 175:2
  @7 = "llvm/test/Transforms/InstSimplify/select.ll":167:1 to 169:32
  @8 = "llvm/test/Transforms/InstSimplify/select.ll":222:1 to 231:2
  @9 = "llvm/test/Transforms/InstSimplify/select.ll":223:1 to 225:33
  @10 = "llvm/test/Transforms/InstSimplify/select.ll":331:1 to 340:2
  @11 = "llvm/test/Transforms/InstSimplify/select.ll":332:1 to 334:33
  @12 = "llvm/test/Transforms/InstSimplify/select.ll":354:1 to 363:2
  @13 = "llvm/test/Transforms/InstSimplify/select.ll":377:1 to 387:2
  @14 = "llvm/test/Transforms/InstSimplify/select.ll":378:1 to 380:32
  @15 = "llvm/test/Transforms/InstSimplify/select.ll":473:1 to 483:2
  @16 = "llvm/test/Transforms/InstSimplify/select.ll":1011:1 to 1020:2
  @17 = "llvm/test/Transforms/InstSimplify/select.ll":1012:1 to 1014:33
  @18 = "llvm/test/Transforms/InstSimplify/select.ll":1066:1 to 1077:2
  @19 = "llvm/test/Transforms/InstSimplify/select.ll":1132:1 to 1143:2
  @20 = "llvm/test/Transforms/InstSimplify/select.ll":1133:1 to 1136:32
  @21 = "llvm/test/Transforms/InstSimplify/select.ll":1195:1 to 1208:2
  @22 = "llvm/test/Transforms/InstSimplify/select.ll":1228:1 to 1237:2
  @23 = "llvm/test/Transforms/InstSimplify/select.ll":1295:1 to 1301:2
  @24 = "llvm/test/Transforms/InstSimplify/select.ll":1303:1 to 1309:2
  @25 = "llvm/test/Transforms/InstSimplify/select.ll":1322:1 to 1333:2
  @26 = "llvm/test/Transforms/InstSimplify/select.ll":1412:1 to 1423:2
  @27 = "llvm/test/Transforms/InstSimplify/select.ll":1442:1 to 1455:2
  @28 = "llvm/test/Transforms/InstSimplify/select.ll":1593:1 to 1602:2
  @29 = "llvm/test/Transforms/InstSimplify/select.ll":1594:1 to 1596:33
}
