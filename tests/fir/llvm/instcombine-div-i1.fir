func @sdiv_by_zero_indirect_is_poison(%c: i1, %x: i1, %y: i1) -> i1 {
^entry:
  cond_br %c, ^true, ^false @0
^true:
  %f1: i1 = const false @0
  %y_true: i1 = and %y, %f1 @0
  br ^done(%y_true) @0
^false:
  %f2: i1 = const false @0
  %y_false: i1 = and %y, %f2 @0
  br ^done(%y_false) @0
^done(%yy: i1):
  %r: i1 = sdiv %x, %yy @0
  ret %r @0
}

func @udiv_by_zero_indirect_is_poison(%c: i1, %x: i1, %y: i1) -> i1 {
^entry:
  cond_br %c, ^true, ^false @1
^true:
  %f1: i1 = const false @1
  %y_true: i1 = and %y, %f1 @1
  br ^done(%y_true) @1
^false:
  %f2: i1 = const false @1
  %y_false: i1 = and %y, %f2 @1
  br ^done(%y_false) @1
^done(%yy: i1):
  %r: i1 = udiv %x, %yy @1
  ret %r @1
}

func @srem_by_zero_indirect_is_poison(%c: i1, %x: i1, %y: i1) -> i1 {
^entry:
  cond_br %c, ^true, ^false @2
^true:
  %f1: i1 = const false @2
  %y_true: i1 = and %y, %f1 @2
  br ^done(%y_true) @2
^false:
  %f2: i1 = const false @2
  %y_false: i1 = and %y, %f2 @2
  br ^done(%y_false) @2
^done(%yy: i1):
  %r: i1 = srem %x, %yy @2
  ret %r @2
}

func @urem_by_zero_indirect_is_poison(%c: i1, %x: i1, %y: i1) -> i1 {
^entry:
  cond_br %c, ^true, ^false @3
^true:
  %f1: i1 = const false @3
  %y_true: i1 = and %y, %f1 @3
  br ^done(%y_true) @3
^false:
  %f2: i1 = const false @3
  %y_false: i1 = and %y, %f2 @3
  br ^done(%y_false) @3
^done(%yy: i1):
  %r: i1 = urem %x, %yy @3
  ret %r @3
}

func @sdiv_i1_is_op0(%x: i1, %y: i1) -> i1 {
^entry:
  %r: i1 = sdiv %x, %y @4
  ret %r @4
}

func @udiv_i1_is_op0(%x: i1, %y: i1) -> i1 {
^entry:
  %r: i1 = udiv %x, %y @5
  ret %r @5
}

func @srem_i1_is_zero(%x: i1, %y: i1) -> i1 {
^entry:
  %r: i1 = srem %x, %y @6
  ret %r @6
}

func @urem_i1_is_zero(%x: i1, %y: i1) -> i1 {
^entry:
  %r: i1 = urem %x, %y @7
  ret %r @7
}

locs {
  @0 = "llvm/test/Transforms/InstCombine/div-i1.ll":4:1 to 25:2
  @1 = "llvm/test/Transforms/InstCombine/div-i1.ll":27:1 to 48:2
  @2 = "llvm/test/Transforms/InstCombine/div-i1.ll":50:1 to 71:2
  @3 = "llvm/test/Transforms/InstCombine/div-i1.ll":73:1 to 94:2
  @4 = "llvm/test/Transforms/InstCombine/div-i1.ll":96:1 to 102:2
  @5 = "llvm/test/Transforms/InstCombine/div-i1.ll":104:1 to 110:2
  @6 = "llvm/test/Transforms/InstCombine/div-i1.ll":112:1 to 118:2
  @7 = "llvm/test/Transforms/InstCombine/div-i1.ll":120:1 to 126:2
}
