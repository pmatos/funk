func @fold(%x: i32) -> i32 {
^entry:
  %y: i32 = freeze %x @0
  %z: i32 = freeze %y @0
  ret %z @0
}

func @fold.folded(%x: i32) -> i32 {
^entry:
  %y: i32 = freeze %x @1
  ret %y @1
}

func @make_const() -> i32 {
^entry:
  %c: i32 = const 10 @2
  %x: i32 = freeze %c @2
  ret %x @2
}

func @icmp(%a: i32, %b: i32) -> i1 {
^entry:
  %a.fr: i32 = freeze %a @3
  %b.fr: i32 = freeze %b @3
  %c: i1 = icmp eq %a.fr, %b.fr @3
  %c.fr: i1 = freeze %c @3
  ret %c.fr @3
}

func @icmp.folded(%a: i32, %b: i32) -> i1 {
^entry:
  %a.fr: i32 = freeze %a @4
  %b.fr: i32 = freeze %b @4
  %c: i1 = icmp eq %a.fr, %b.fr @4
  ret %c @4
}

func @icmp_noopt(%a: i32, %b: i32) -> i1 {
^entry:
  %c: i1 = icmp eq %a, %b @5
  %c.fr: i1 = freeze %c @5
  ret %c.fr @5
}

func @brcond(%c: i1, %c2: i1) -> i1 {
^entry:
  cond_br %c, ^A, ^B @6
^A:
  cond_br %c2, ^A2, ^B @6
^A2:
  %f1: i1 = freeze %c @6
  ret %f1 @6
^B:
  %f2: i1 = freeze %c @6
  ret %f2 @6
}

func @brcond.folded(%c: i1, %c2: i1) -> i1 {
^entry:
  cond_br %c, ^A, ^B @7
^A:
  cond_br %c2, ^A2, ^B @7
^A2:
  ret %c @7
^B:
  ret %c @7
}

func @phi(%cond: i1, %cond2: i1, %a0: i32, %a1: i32) -> i32 {
^ENTRY:
  %a0.fr: i32 = freeze %a0 @8
  cond_br %cond, ^BB1, ^BB2(%a0.fr) @8
^BB1:
  %a1.fr: i32 = freeze %a1 @8
  cond_br %cond2, ^BB2(%a1.fr), ^EXIT(%a0.fr) @8
^BB2(%phi1: i32):
  br ^EXIT(%phi1) @8
^EXIT(%phi2: i32):
  %phi2.fr: i32 = freeze %phi2 @8
  ret %phi2.fr @8
}

func @phi.folded(%cond: i1, %cond2: i1, %a0: i32, %a1: i32) -> i32 {
^ENTRY:
  %a0.fr: i32 = freeze %a0 @9
  cond_br %cond, ^BB1, ^BB2(%a0.fr) @9
^BB1:
  %a1.fr: i32 = freeze %a1 @9
  cond_br %cond2, ^BB2(%a1.fr), ^EXIT(%a0.fr) @9
^BB2(%phi1: i32):
  br ^EXIT(%phi1) @9
^EXIT(%phi2: i32):
  ret %phi2 @9
}

func @phi_noopt(%cond: i1, %cond2: i1, %a0: i32, %a1: i32) -> i32 {
^ENTRY:
  %a0.fr: i32 = freeze %a0 @10
  cond_br %cond, ^BB1, ^BB2(%a0.fr) @10
^BB1:
  cond_br %cond2, ^BB2(%a1), ^EXIT(%a0.fr) @10
^BB2(%phi1: i32):
  br ^EXIT(%phi1) @10
^EXIT(%phi2: i32):
  %phi2.fr: i32 = freeze %phi2 @10
  ret %phi2.fr @10
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/freeze.ll":4:1 to 12:2
  @1 = "llvm/test/Transforms/InstSimplify/freeze.ll":5:1 to 7:31
  @2 = "llvm/test/Transforms/InstSimplify/freeze.ll":14:1 to 20:2
  @3 = "llvm/test/Transforms/InstSimplify/freeze.ll":309:1 to 321:2
  @4 = "llvm/test/Transforms/InstSimplify/freeze.ll":310:1 to 314:30
  @5 = "llvm/test/Transforms/InstSimplify/freeze.ll":323:1 to 332:2
  @6 = "llvm/test/Transforms/InstSimplify/freeze.ll":363:1 to 382:2
  @7 = "llvm/test/Transforms/InstSimplify/freeze.ll":364:1 to 371:30
  @8 = "llvm/test/Transforms/InstSimplify/freeze.ll":384:1 to 412:2
  @9 = "llvm/test/Transforms/InstSimplify/freeze.ll":385:1 to 397:34
  @10 = "llvm/test/Transforms/InstSimplify/freeze.ll":414:1 to 441:2
}
