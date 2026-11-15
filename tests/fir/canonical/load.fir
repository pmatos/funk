func @fresh() -> i32 {
^entry:
  %p: ptr = alloca stack i32 @0
  %v: i32 = load nonatomic %p @0
  ret %v @0
}

func @fresh_odd() -> i1 {
^entry:
  %p: ptr = alloca stack i8 @0
  %v: i1 = load nonatomic %p @0
  ret %v @0
}

func @at(%k: i64) -> i8 {
^entry:
  %p: ptr = alloca stack i8 8 align(4) @0
  %q: ptr = ptradd %p, %k @0
  %v: i8 = load nonatomic %q @0
  ret %v @0
}

func @misaligned() -> i32 {
^entry:
  %p: ptr = alloca stack i8 16 @0
  %v: i32 = load nonatomic %p @0
  ret %v @0
}

func @aligned() -> i32 {
^entry:
  %p: ptr = alloca stack i8 16 align(4) @0
  %v: i32 = load nonatomic %p @0
  ret %v @0
}

func @promised(%k: i64) -> i32 {
^entry:
  %p: ptr = alloca stack i8 16 @0
  %q: ptr = ptradd %p, %k @0
  %v: i32 = load nonatomic align(1) %q @0
  ret %v @0
}

func @widest_align() -> i64 {
^entry:
  %p: ptr = alloca stack i64 align(8388608) @0
  %v: i64 = load nonatomic align(8388608) %p @0
  ret %v @0
}

func @escape() -> ptr {
^entry:
  %p: ptr = alloca stack i32 @0
  ret %p @0
}

func @freed() -> i32 {
^entry:
  %p: ptr = call @escape @0
  %v: i32 = load nonatomic %p @0
  ret %v @0
}

func @through(%p: ptr) -> i16 {
^entry:
  %v: i16 = load nonatomic %p @0
  ret %v @0
}

locs {
  @0 = unknown
}
