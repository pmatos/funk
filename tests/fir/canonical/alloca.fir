func @one() -> ptr {
^entry:
  %p: ptr = alloca stack i32 @0
  ret %p @0
}

func @four() -> ptr {
^entry:
  %p: ptr = alloca stack i32 4 @0
  ret %p @0
}

func @bytes() -> ptr {
^entry:
  %p: ptr = alloca stack i8 12 align(4) @0
  ret %p @0
}

func @two() -> ptr {
^entry:
  %p: ptr = alloca stack i64 @0
  %q: ptr = alloca stack i64 @0
  ret %q @0
}

func @moved(%k: i64) -> ptr {
^entry:
  %p: ptr = alloca stack i128 2 align(16) @0
  %q: ptr = ptradd %p, %k @0
  ret %q @0
}

func @callee() -> i1 {
^entry:
  %p: ptr = alloca stack i16 @0
  %t: i1 = const true @0
  ret %t @0
}

func @after_call() -> ptr {
^entry:
  %c: i1 = call @callee @0
  %p: ptr = alloca stack i7 3 @0
  ret %p @0
}

func @loop(%n: i8) -> ptr {
^entry:
  %z: i8 = const 0 @0
  %p0: ptr = alloca stack i1 @0
  br ^head(%z, %p0) @0
^head(%i: i8, %p: ptr):
  %done: i1 = icmp eq %i, %n @0
  cond_br %done, ^exit, ^body @0
^body:
  %q: ptr = alloca stack i33 @0
  %one: i8 = const 1 @0
  %j: i8 = add %i, %one @0
  br ^head(%j, %q) @0
^exit:
  ret %p @0
}

locs {
  @0 = unknown
}
