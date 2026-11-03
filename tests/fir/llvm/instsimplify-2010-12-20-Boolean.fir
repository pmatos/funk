func @add(%x: i1) -> i1 {
^entry:
  %z: i1 = add %x, %x @0
  ret %z @0
}

func @sub(%x: i1) -> i1 {
^entry:
  %f: i1 = const false @1
  %z: i1 = sub %f, %x @1
  ret %z @1
}

func @mul(%x: i1) -> i1 {
^entry:
  %z: i1 = mul %x, %x @2
  ret %z @2
}

func @ne(%x: i1) -> i1 {
^entry:
  %f: i1 = const false @3
  %z: i1 = icmp ne %x, %f @3
  ret %z @3
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/2010-12-20-Boolean.ll":4:1 to 10:2
  @1 = "llvm/test/Transforms/InstSimplify/2010-12-20-Boolean.ll":12:1 to 18:2
  @2 = "llvm/test/Transforms/InstSimplify/2010-12-20-Boolean.ll":20:1 to 26:2
  @3 = "llvm/test/Transforms/InstSimplify/2010-12-20-Boolean.ll":28:1 to 34:2
}
