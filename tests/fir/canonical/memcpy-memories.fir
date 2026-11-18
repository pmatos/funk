layout memory(1, unit(16), pointer(32), little)

func @two_units(%v: i32, %n: i16) -> i32 {
^entry:
  %p: ptr(1) = alloca stack i32 2 @0
  store nonatomic %v, %p @0
  %two: i16 = const 2 @0
  %q: ptr(1) = ptradd %p, %two @0
  memcpy nonatomic %q, %p, %n @0
  %w: i32 = load nonatomic %q @0
  ret %w @0
}

func @move_unit(%v: i32) -> i32 {
^entry:
  %p: ptr(1) = alloca stack i32 2 @1
  store nonatomic %v, %p @1
  %one: i8 = const 1 @1
  %q: ptr(1) = ptradd %p, %one @1
  %two: i8 = const 2 @1
  memmove nonatomic %q, %p, %two @1
  %w: i32 = load nonatomic align(1) %q @1
  ret %w @1
}

func @past(%n: i32) -> i32 {
^entry:
  %p: ptr(1) = alloca stack i32 @2
  %q: ptr(1) = alloca stack i32 @2
  memmove nonatomic %q, %p, %n @2
  ret %n @2
}

locs {
  @0 = unknown
  @1 = unknown
  @2 = unknown
}
