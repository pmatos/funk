func @shl_by_bitwidth(%A: i32) -> i32 {
^entry:
  %c: i32 = const 32 @0
  %B: i32 = shl %A, %c @0
  ret %B @0
}

func @ashr_all_ones(%A: i32) -> i32 {
^entry:
  %m: i32 = const -1 @1
  %B: i32 = ashr %m, %A @1
  ret %B @1
}

func @lshr_by_sext_bool(%x: i1, %y: i8) -> i8 {
^entry:
  %s: i8 = sext %x @2
  %r: i8 = lshr %y, %s @2
  ret %r @2
}

func @ashr_by_sext_bool(%x: i1, %y: i8) -> i8 {
^entry:
  %s: i8 = sext %x @3
  %r: i8 = ashr %y, %s @3
  ret %r @3
}

func @shl_by_sext_bool(%x: i1, %y: i8) -> i8 {
^entry:
  %s: i8 = sext %x @4
  %r: i8 = shl %y, %s @4
  ret %r @4
}

func @shl_or_shr(%a: i32, %b: i32) -> i64 {
^entry:
  %t1: i64 = zext %a @5
  %t2: i64 = zext %b @5
  %c: i64 = const 32 @5
  %t3: i64 = shl %t1, %c @5
  %t4: i64 = or %t2, %t3 @5
  %t5: i64 = lshr %t4, %c @5
  ret %t5 @5
}

func @shl_or_shr.folded(%a: i32, %b: i32) -> i64 {
^entry:
  %t1: i64 = zext %a @6
  ret %t1 @6
}

func @shl_or_shr2(%a: i32, %b: i32) -> i64 {
^entry:
  %t1: i64 = zext %a @7
  %t2: i64 = zext %b @7
  %c: i64 = const 31 @7
  %t3: i64 = shl %t1, %c @7
  %t4: i64 = or %t2, %t3 @7
  %t5: i64 = lshr %t4, %c @7
  ret %t5 @7
}

func @poison(%x: i32) -> i32 {
^entry:
  %n: i32 = const 32 @8
  %p: i32 = shl %n, %n @8
  %v: i32 = lshr %x, %p @8
  ret %v @8
}

func @poison2(%x: i32) -> i32 {
^entry:
  %n: i32 = const 32 @9
  %p: i32 = shl %n, %n @9
  %v: i32 = ashr %x, %p @9
  ret %v @9
}

func @poison3(%x: i32) -> i32 {
^entry:
  %n: i32 = const 32 @10
  %p: i32 = shl %n, %n @10
  %v: i32 = shl %x, %p @10
  ret %v @10
}

func @poison4(%x: i32) -> i32 {
^entry:
  %n: i32 = const 32 @11
  %p: i32 = shl %n, %n @11
  %v: i32 = lshr %p, %x @11
  ret %v @11
}

func @poison5(%x: i32) -> i32 {
^entry:
  %n: i32 = const 32 @12
  %p: i32 = shl %n, %n @12
  %v: i32 = ashr %p, %x @12
  ret %v @12
}

func @poison6(%x: i32) -> i32 {
^entry:
  %n: i32 = const 32 @13
  %p: i32 = shl %n, %n @13
  %v: i32 = shl %p, %x @13
  ret %v @13
}

func @all_ones_left_right(%x: i32) -> i32 {
^entry:
  %m: i32 = const -1 @14
  %left: i32 = shl %m, %x @14
  %right: i32 = ashr %left, %x @14
  ret %right @14
}

func @almost_all_ones_left_right(%x: i32) -> i32 {
^entry:
  %m: i32 = const -2 @15
  %left: i32 = shl %m, %x @15
  %right: i32 = ashr %left, %x @15
  ret %right @15
}

func @all_ones_left_right_not_same_shift(%x: i32, %y: i32) -> i32 {
^entry:
  %m: i32 = const -1 @16
  %left: i32 = shl %m, %x @16
  %right: i32 = ashr %left, %y @16
  ret %right @16
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/shift.ll":60:1 to 66:2
  @1 = "llvm/test/Transforms/InstSimplify/shift.ll":108:1 to 114:2
  @2 = "llvm/test/Transforms/InstSimplify/shift.ll":124:1 to 131:2
  @3 = "llvm/test/Transforms/InstSimplify/shift.ll":142:1 to 149:2
  @4 = "llvm/test/Transforms/InstSimplify/shift.ll":160:1 to 167:2
  @5 = "llvm/test/Transforms/InstSimplify/shift.ll":178:1 to 189:2
  @6 = "llvm/test/Transforms/InstSimplify/shift.ll":179:1 to 181:32
  @7 = "llvm/test/Transforms/InstSimplify/shift.ll":192:1 to 207:2
  @8 = "llvm/test/Transforms/InstSimplify/shift.ll":241:1 to 247:2
  @9 = "llvm/test/Transforms/InstSimplify/shift.ll":249:1 to 255:2
  @10 = "llvm/test/Transforms/InstSimplify/shift.ll":257:1 to 263:2
  @11 = "llvm/test/Transforms/InstSimplify/shift.ll":265:1 to 271:2
  @12 = "llvm/test/Transforms/InstSimplify/shift.ll":273:1 to 279:2
  @13 = "llvm/test/Transforms/InstSimplify/shift.ll":281:1 to 287:2
  @14 = "llvm/test/Transforms/InstSimplify/shift.ll":289:1 to 296:2
  @15 = "llvm/test/Transforms/InstSimplify/shift.ll":331:1 to 340:2
  @16 = "llvm/test/Transforms/InstSimplify/shift.ll":344:1 to 353:2
}
