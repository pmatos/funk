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

func @test3.folded(%x: i32) -> i32 {
^entry:
  %m2: i32 = const -2 @6
  %and1: i32 = and %x, %m2 @6
  ret %and1 @6
}

func @test4(%X: i32) -> i32 {
^entry:
  %k: i32 = const 0 @7
  %cmp: i1 = icmp slt %X, %k @7
  %c: i32 = const -2147483648 @7
  %or: i32 = or %X, %c @7
  %cond: i32 = select %cmp, %X, %or @7
  ret %cond @7
}

func @test4.folded(%X: i32) -> i32 {
^entry:
  %c: i32 = const -2147483648 @8
  %or: i32 = or %X, %c @8
  ret %or @8
}

func @test6(%X: i32) -> i32 {
^entry:
  %k: i32 = const 0 @9
  %cmp: i1 = icmp slt %X, %k @9
  %c: i32 = const 2147483647 @9
  %and: i32 = and %X, %c @9
  %cond: i32 = select %cmp, %and, %X @9
  ret %cond @9
}

func @test6.folded(%X: i32) -> i32 {
^entry:
  %c: i32 = const 2147483647 @10
  %and: i32 = and %X, %c @10
  ret %and @10
}

func @test12(%X: i32) -> i32 {
^entry:
  %k: i32 = const 4 @11
  %cmp: i1 = icmp ult %X, %k @11
  %c: i32 = const 3 @11
  %and: i32 = and %X, %c @11
  %cond: i32 = select %cmp, %X, %and @11
  ret %cond @11
}

func @test12.folded(%X: i32) -> i32 {
^entry:
  %c: i32 = const 3 @12
  %and: i32 = and %X, %c @12
  ret %and @12
}

func @test13(%X: i32) -> i32 {
^entry:
  %k: i32 = const 3 @13
  %cmp: i1 = icmp ugt %X, %k @13
  %c: i32 = const 3 @13
  %and: i32 = and %X, %c @13
  %cond: i32 = select %cmp, %and, %X @13
  ret %cond @13
}

func @test13.folded(%X: i32) -> i32 {
^entry:
  %c: i32 = const 3 @14
  %and: i32 = and %X, %c @14
  ret %and @14
}

func @select_icmp_and_8_eq_0_or_8(%x: i32) -> i32 {
^entry:
  %c8: i32 = const 8 @15
  %and: i32 = and %x, %c8 @15
  %zero: i32 = const 0 @15
  %cmp: i1 = icmp eq %and, %zero @15
  %or: i32 = or %x, %c8 @15
  %sel: i32 = select %cmp, %or, %x @15
  ret %sel @15
}

func @select_icmp_and_8_eq_0_or_8.folded(%x: i32) -> i32 {
^entry:
  %c8: i32 = const 8 @16
  %or: i32 = or %x, %c8 @16
  ret %or @16
}

func @select_icmp_trunc_8_ne_0_or_128(%x: i32) -> i32 {
^entry:
  %trunc: i8 = trunc %x @17
  %m1: i8 = const -1 @17
  %cmp: i1 = icmp sgt %trunc, %m1 @17
  %c128: i32 = const 128 @17
  %or: i32 = or %x, %c128 @17
  %sel: i32 = select %cmp, %or, %x @17
  ret %sel @17
}

func @select_icmp_trunc_8_ne_0_or_128.folded(%x: i32) -> i32 {
^entry:
  %c128: i32 = const 128 @18
  %or: i32 = or %x, %c128 @18
  ret %or @18
}

func @select_neutral_add_rhs(%x: i32, %y: i32) -> i32 {
^entry:
  %zero: i32 = const 0 @19
  %cmp: i1 = icmp ne %y, %zero @19
  %add: i32 = add %x, %y @19
  %sel: i32 = select %cmp, %add, %x @19
  ret %sel @19
}

func @select_neutral_add_rhs.folded(%x: i32, %y: i32) -> i32 {
^entry:
  %add: i32 = add %x, %y @20
  ret %add @20
}

func @select_neutral_sub_lhs(%x: i32, %y: i32) -> i32 {
^entry:
  %zero: i32 = const 0 @21
  %cmp: i1 = icmp ne %y, %zero @21
  %add: i32 = sub %y, %x @21
  %sel: i32 = select %cmp, %add, %x @21
  ret %sel @21
}

func @select_eq_xor_recursive(%a: i8, %b: i8) -> i8 {
^entry:
  %xor: i8 = xor %a, %b @22
  %m1: i8 = const -1 @22
  %inv: i8 = xor %xor, %m1 @22
  %cmp: i1 = icmp eq %a, %b @22
  %sel: i8 = select %cmp, %m1, %inv @22
  ret %sel @22
}

func @select_eq_xor_recursive.folded(%a: i8, %b: i8) -> i8 {
^entry:
  %xor: i8 = xor %a, %b @23
  %m1: i8 = const -1 @23
  %inv: i8 = xor %xor, %m1 @23
  ret %inv @23
}

func @select_eq_and_recursive(%a: i8) -> i8 {
^entry:
  %zero: i8 = const 0 @24
  %neg: i8 = sub %zero, %a @24
  %and: i8 = and %neg, %a @24
  %one: i8 = const 1 @24
  %add: i8 = add %and, %one @24
  %cmp: i1 = icmp eq %a, %zero @24
  %sel: i8 = select %cmp, %one, %add @24
  ret %sel @24
}

func @select_eq_and_recursive.folded(%a: i8) -> i8 {
^entry:
  %zero: i8 = const 0 @25
  %neg: i8 = sub %zero, %a @25
  %and: i8 = and %neg, %a @25
  %one: i8 = const 1 @25
  %add: i8 = add %and, %one @25
  ret %add @25
}

func @select_eq_xor_recursive_allow_refinement(%a: i8, %b: i8) -> i8 {
^entry:
  %xor1: i8 = add %a, %b @26
  %xor2: i8 = xor %a, %xor1 @26
  %zero: i8 = const 0 @26
  %cmp: i1 = icmp eq %b, %zero @26
  %sel: i8 = select %cmp, %xor2, %zero @26
  ret %sel @26
}

func @poison2(%cond: i1, %x: i32) -> i32 {
^entry:
  %n: i32 = const 32 @27
  %p: i32 = shl %n, %n @27
  %v: i32 = select %cond, %p, %x @27
  ret %v @27
}

func @poison3(%cond: i1, %x: i32) -> i32 {
^entry:
  %n: i32 = const 32 @28
  %p: i32 = shl %n, %n @28
  %v: i32 = select %cond, %x, %p @28
  ret %v @28
}

func @replace_false_op_eq_neg_and(%x: i8) -> i8 {
^entry:
  %zero: i8 = const 0 @29
  %eq0: i1 = icmp eq %x, %zero @29
  %neg: i8 = sub %zero, %x @29
  %and: i8 = and %neg, %x @29
  %sel: i8 = select %eq0, %zero, %and @29
  ret %sel @29
}

func @replace_false_op_eq_neg_and.folded(%x: i8) -> i8 {
^entry:
  %zero: i8 = const 0 @30
  %neg: i8 = sub %zero, %x @30
  %and: i8 = and %neg, %x @30
  ret %and @30
}

func @replace_false_op_eq_shl_or(%x: i8) -> i8 {
^entry:
  %m1: i8 = const -1 @31
  %eq0: i1 = icmp eq %x, %m1 @31
  %c3: i8 = const 3 @31
  %shl: i8 = shl %x, %c3 @31
  %or: i8 = or %x, %shl @31
  %sel: i8 = select %eq0, %m1, %or @31
  ret %sel @31
}

func @replace_false_op_eq_shl_or.folded(%x: i8) -> i8 {
^entry:
  %c3: i8 = const 3 @32
  %shl: i8 = shl %x, %c3 @32
  %or: i8 = or %x, %shl @32
  ret %or @32
}

func @replace_false_op_sgt_neg_and(%x: i8) -> i8 {
^entry:
  %zero: i8 = const 0 @33
  %eq0: i1 = icmp sgt %x, %zero @33
  %neg: i8 = sub %zero, %x @33
  %and: i8 = and %neg, %x @33
  %sel: i8 = select %eq0, %zero, %and @33
  ret %sel @33
}

func @select_sub_cmp(%0: i8, %1: i8) -> i8 {
^entry:
  %3: i1 = icmp eq %1, %0 @34
  %4: i8 = sub nsw %1, %0 @34
  %z: i8 = const 0 @34
  %5: i8 = select %3, %z, %4 @34
  ret %5 @34
}

func @select_sub_cmp.folded(%0: i8, %1: i8) -> i8 {
^entry:
  %4: i8 = sub nsw %1, %0 @35
  ret %4 @35
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/select.ll":4:1 to 10:2
  @1 = "llvm/test/Transforms/InstSimplify/select.ll":36:1 to 42:2
  @2 = "llvm/test/Transforms/InstSimplify/select.ll":44:1 to 50:2
  @3 = "llvm/test/Transforms/InstSimplify/select.ll":52:1 to 58:2
  @4 = "llvm/test/Transforms/InstSimplify/select.ll":132:1 to 141:2
  @5 = "llvm/test/Transforms/InstSimplify/select.ll":154:1 to 164:2
  @6 = "llvm/test/Transforms/InstSimplify/select.ll":155:1 to 157:34
  @7 = "llvm/test/Transforms/InstSimplify/select.ll":166:1 to 175:2
  @8 = "llvm/test/Transforms/InstSimplify/select.ll":167:1 to 169:32
  @9 = "llvm/test/Transforms/InstSimplify/select.ll":222:1 to 231:2
  @10 = "llvm/test/Transforms/InstSimplify/select.ll":223:1 to 225:33
  @11 = "llvm/test/Transforms/InstSimplify/select.ll":331:1 to 340:2
  @12 = "llvm/test/Transforms/InstSimplify/select.ll":332:1 to 334:33
  @13 = "llvm/test/Transforms/InstSimplify/select.ll":354:1 to 363:2
  @14 = "llvm/test/Transforms/InstSimplify/select.ll":355:1 to 357:33
  @15 = "llvm/test/Transforms/InstSimplify/select.ll":377:1 to 387:2
  @16 = "llvm/test/Transforms/InstSimplify/select.ll":378:1 to 380:32
  @17 = "llvm/test/Transforms/InstSimplify/select.ll":473:1 to 483:2
  @18 = "llvm/test/Transforms/InstSimplify/select.ll":474:1 to 476:32
  @19 = "llvm/test/Transforms/InstSimplify/select.ll":1011:1 to 1020:2
  @20 = "llvm/test/Transforms/InstSimplify/select.ll":1012:1 to 1014:33
  @21 = "llvm/test/Transforms/InstSimplify/select.ll":1066:1 to 1077:2
  @22 = "llvm/test/Transforms/InstSimplify/select.ll":1132:1 to 1143:2
  @23 = "llvm/test/Transforms/InstSimplify/select.ll":1133:1 to 1136:32
  @24 = "llvm/test/Transforms/InstSimplify/select.ll":1195:1 to 1208:2
  @25 = "llvm/test/Transforms/InstSimplify/select.ll":1196:1 to 1200:32
  @26 = "llvm/test/Transforms/InstSimplify/select.ll":1228:1 to 1237:2
  @27 = "llvm/test/Transforms/InstSimplify/select.ll":1295:1 to 1301:2
  @28 = "llvm/test/Transforms/InstSimplify/select.ll":1303:1 to 1309:2
  @29 = "llvm/test/Transforms/InstSimplify/select.ll":1322:1 to 1333:2
  @30 = "llvm/test/Transforms/InstSimplify/select.ll":1323:1 to 1326:32
  @31 = "llvm/test/Transforms/InstSimplify/select.ll":1412:1 to 1423:2
  @32 = "llvm/test/Transforms/InstSimplify/select.ll":1413:1 to 1416:31
  @33 = "llvm/test/Transforms/InstSimplify/select.ll":1442:1 to 1455:2
  @34 = "llvm/test/Transforms/InstSimplify/select.ll":1593:1 to 1602:2
  @35 = "llvm/test/Transforms/InstSimplify/select.ll":1594:1 to 1596:33
}
