func @fill(%v: i8) -> i32 {
^entry:
  %p: ptr = alloca stack i32 @0
  %four: i64 = const 4 @0
  memset nonatomic %p, %v, %four @0
  %w: i32 = load nonatomic %p @0
  ret %w @0
}

func @fill_part(%v: i8, %n: i64) -> i32 {
^entry:
  %p: ptr = alloca stack i32 @1
  %x: i32 = const 67305985 @1
  store nonatomic %x, %p @1
  memset nonatomic %p, %v, %n @1
  %w: i32 = load nonatomic %p @1
  ret %w @1
}

func @fill_ptr() -> i32 {
^entry:
  %a: ptr = alloca stack i32 @2
  %s: ptr = alloca stack ptr @2
  store nonatomic %a, %s @2
  %z: i8 = const 0 @2
  %one: i64 = const 1 @2
  memset nonatomic %s, %z, %one @2
  %b: ptr = load nonatomic %s @2
  %w: i32 = load nonatomic %b @2
  ret %w @2
}

func @fill_poison() -> i32 {
^entry:
  %p: ptr = alloca stack i32 @3
  %x: i32 = const 1 @3
  store nonatomic %x, %p @3
  %v: i8 = poison @3
  %two: i64 = const 2 @3
  memset nonatomic %p, %v, %two @3
  %w: i32 = load nonatomic %p @3
  ret %w @3
}

func @frame() -> ptr {
^entry:
  %p: ptr = alloca stack i32 @4
  ret %p @4
}

func @through(%p: ptr, %v: i8, %n: i64) -> i64 {
^entry:
  memset nonatomic %p, %v, %n @4
  ret %n @4
}

func @dangling(%n: i8) -> i8 {
^entry:
  %p: ptr = call @frame @4
  %v: i8 = const 1 @4
  memset nonatomic %p, %v, %n @4
  ret %n @4
}

func @huge() -> i32 {
^entry:
  %p: ptr = alloca stack i8 4 @5
  %v: i8 = const 1 @5
  %n: i64 = const -9223372036854775808 @5
  memset nonatomic %p, %v, %n @5
  %w: i32 = load nonatomic %p @5
  ret %w @5
}

func @past(%k: i64, %n: i64) -> i64 {
^entry:
  %p: ptr = alloca stack i32 @6
  %q: ptr = ptradd %p, %k @6
  %v: i8 = const 1 @6
  memset nonatomic %q, %v, %n @6
  ret %n @6
}

func @poison_length(%n: i1) -> i8 {
^entry:
  %p: ptr = alloca stack i8 @7
  %v: i8 = const 7 @7
  memset nonatomic %p, %v, %n @7
  %w: i8 = load nonatomic %p @7
  ret %w @7
}

func @poison_length_ub(%n: i8) -> i8 {
^entry:
  %p: ptr = alloca stack i8 @7
  %v: i8 = const 7 @7
  store nonatomic %v, %p @7
  memset nonatomic %p, %v, %n @7
  %w: i8 = load nonatomic %p @7
  ret %w @7
}

func @lengths(%v: i8) -> i32 {
^entry:
  %p: ptr = alloca stack i32 @8
  %one: i1 = const true @8
  memset nonatomic %p, %v, %one @8
  %a: i7 = const 2 @8
  memset nonatomic %p, %v, %a @8
  %b: i33 = const 3 @8
  memset nonatomic %p, %v, %b @8
  %c: i128 = const 4 @8
  memset nonatomic %p, %v, %c @8
  %w: i32 = load nonatomic %p @8
  ret %w @8
}

locs {
  @0 = unknown
  @1 = unknown
  @2 = unknown
  @3 = unknown
  @4 = unknown
  @5 = unknown
  @6 = unknown
  @7 = unknown
  @8 = unknown
}
