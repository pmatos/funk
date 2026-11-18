func @copy_int(%v: i32) -> i32 {
^entry:
  %p: ptr = alloca stack i32 2 @0
  store nonatomic %v, %p @0
  %four: i64 = const 4 @0
  %q: ptr = ptradd %p, %four @0
  memcpy nonatomic %q, %p, %four @0
  %w: i32 = load nonatomic %q @0
  ret %w @0
}

func @copy_ptr(%v: i32) -> i32 {
^entry:
  %a: ptr = alloca stack i32 @1
  store nonatomic %v, %a @1
  %s: ptr = alloca stack ptr 2 @1
  store nonatomic %a, %s @1
  %eight: i8 = const 8 @1
  %t: ptr = ptradd %s, %eight @1
  memcpy nonatomic %t, %s, %eight @1
  %b: ptr = load nonatomic %t @1
  %w: i32 = load nonatomic %b @1
  ret %w @1
}

func @move_ptr(%v: i32) -> i32 {
^entry:
  %a: ptr = alloca stack i32 @1
  store nonatomic %v, %a @1
  %s: ptr = alloca stack ptr 2 @1
  store nonatomic %a, %s @1
  %eight: i64 = const 8 @1
  %t: ptr = ptradd %s, %eight @1
  memmove nonatomic %t, %s, %eight @1
  %b: ptr = load nonatomic %t @1
  %w: i32 = load nonatomic %b @1
  ret %w @1
}

func @copy_part_ptr(%n: i64) -> ptr {
^entry:
  %a: ptr = alloca stack i32 @2
  %s: ptr = alloca stack ptr 2 @2
  store nonatomic %a, %s @2
  %eight: i64 = const 8 @2
  %t: ptr = ptradd %s, %eight @2
  memcpy nonatomic %t, %s, %n @2
  %b: ptr = load nonatomic %t @2
  ret %b @2
}

func @copy_poison() -> i32 {
^entry:
  %p: ptr = alloca stack i32 2 @3
  %x: i32 = poison @3
  store nonatomic %x, %p @3
  %four: i64 = const 4 @3
  %q: ptr = ptradd %p, %four @3
  %one: i32 = const 1 @3
  store nonatomic %one, %q @3
  memcpy nonatomic %q, %p, %four @3
  %w: i32 = load nonatomic %q @3
  ret %w @3
}

func @copy_fresh() -> i32 {
^entry:
  %p: ptr = alloca stack i32 2 @3
  %four: i64 = const 4 @3
  %q: ptr = ptradd %p, %four @3
  %one: i32 = const 1 @3
  store nonatomic %one, %q @3
  memcpy nonatomic %q, %p, %four @3
  %w: i32 = load nonatomic %q @3
  ret %w @3
}

func @move_up(%v: i32) -> i32 {
^entry:
  %p: ptr = alloca stack i32 @4
  store nonatomic %v, %p @4
  %one: i64 = const 1 @4
  %three: i64 = const 3 @4
  %q: ptr = ptradd %p, %one @4
  memmove nonatomic %q, %p, %three @4
  %w: i32 = load nonatomic %p @4
  ret %w @4
}

func @move_down(%v: i32) -> i32 {
^entry:
  %p: ptr = alloca stack i32 @4
  store nonatomic %v, %p @4
  %one: i64 = const 1 @4
  %three: i64 = const 3 @4
  %q: ptr = ptradd %p, %one @4
  memmove nonatomic %p, %q, %three @4
  %w: i32 = load nonatomic %p @4
  ret %w @4
}

func @copy_at(%k: i64, %n: i64) -> i32 {
^entry:
  %p: ptr = alloca stack i32 2 @5
  %v: i32 = const 67305985 @5
  store nonatomic %v, %p @5
  %q: ptr = ptradd %p, %k @5
  memcpy nonatomic %q, %p, %n @5
  %w: i32 = load nonatomic %p @5
  ret %w @5
}

func @frame() -> ptr {
^entry:
  %p: ptr = alloca stack i32 @6
  ret %p @6
}

func @through(%d: ptr, %s: ptr, %n: i64) -> i64 {
^entry:
  memcpy nonatomic %d, %s, %n @6
  memmove nonatomic %d, %s, %n @6
  ret %n @6
}

func @dangling(%n: i8) -> i8 {
^entry:
  %p: ptr = call @frame @6
  %a: ptr = alloca stack i32 @6
  memcpy nonatomic %a, %p, %n @6
  memmove nonatomic %p, %a, %n @6
  ret %n @6
}

func @huge() -> i32 {
^entry:
  %p: ptr = alloca stack i8 4 @7
  %two: i64 = const 2 @7
  %q: ptr = ptradd %p, %two @7
  %n: i64 = const -9223372036854775808 @7
  memmove nonatomic %q, %p, %n @7
  %w: i32 = load nonatomic %p @7
  ret %w @7
}

func @poison_length(%n: i1) -> i8 {
^entry:
  %p: ptr = alloca stack i8 @8
  %v: i8 = const 7 @8
  store nonatomic %v, %p @8
  memmove nonatomic %p, %p, %n @8
  %w: i8 = load nonatomic %p @8
  ret %w @8
}

func @poison_length_ub(%n: i8) -> i8 {
^entry:
  %p: ptr = alloca stack i8 @8
  %v: i8 = const 7 @8
  store nonatomic %v, %p @8
  memcpy nonatomic %p, %p, %n @8
  %w: i8 = load nonatomic %p @8
  ret %w @8
}

func @lengths(%v: i32) -> i32 {
^entry:
  %p: ptr = alloca stack i32 2 @9
  store nonatomic %v, %p @9
  %four: i64 = const 4 @9
  %q: ptr = ptradd %p, %four @9
  %one: i1 = const true @9
  memcpy nonatomic %q, %p, %one @9
  %a: i7 = const 2 @9
  memcpy nonatomic %q, %p, %a @9
  memmove nonatomic %q, %p, %a @9
  %b: i16 = const 3 @9
  memmove nonatomic %q, %p, %b @9
  %c: i33 = const 4 @9
  memcpy nonatomic %q, %p, %c @9
  memmove nonatomic %q, %p, %c @9
  %d: i128 = const 4 @9
  memcpy nonatomic %q, %p, %d @9
  memmove nonatomic %p, %q, %d @9
  %w: i32 = load nonatomic %q @9
  ret %w @9
}

func @copy_from(%k: i64, %n: i64) -> i64 {
^entry:
  %p: ptr = alloca stack i32 2 @10
  %q: ptr = ptradd %p, %k @10
  memcpy nonatomic %p, %q, %n @10
  ret %n @10
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
  @9 = unknown
  @10 = unknown
}
