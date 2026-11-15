func @round_trip(%v: i32) -> i32 {
^entry:
  %p: ptr = alloca stack i32 @0
  store nonatomic %v, %p @0
  %w: i32 = load nonatomic %p @0
  ret %w @0
}

func @padding(%v: i1) -> i8 {
^entry:
  %p: ptr = alloca stack i8 @0
  store nonatomic %v, %p @0
  %w: i8 = load nonatomic %p @0
  ret %w @0
}

func @narrower(%v: i32) -> i16, i8 {
^entry:
  %p: ptr = alloca stack i32 @0
  store nonatomic %v, %p @0
  %lo: i16 = load nonatomic %p @0
  %one: i64 = const 1 @0
  %q: ptr = ptradd %p, %one @0
  %b: i8 = load nonatomic %q @0
  ret %lo, %b @0
}

func @wider(%v: i32) -> i64 {
^entry:
  %p: ptr = alloca stack i32 2 @0
  store nonatomic %v, %p @0
  %w: i64 = load nonatomic align(4) %p @0
  ret %w @0
}

func @past_end(%v: i32) -> i64 {
^entry:
  %p: ptr = alloca stack i32 @0
  store nonatomic %v, %p @0
  %w: i64 = load nonatomic align(4) %p @0
  ret %w @0
}

func @overwrite(%v: i32, %b: i8) -> i32 {
^entry:
  %p: ptr = alloca stack i32 @0
  store nonatomic %v, %p @0
  %one: i64 = const 1 @0
  %q: ptr = ptradd %p, %one @0
  store nonatomic %b, %q @0
  %w: i32 = load nonatomic %p @0
  ret %w @0
}

func @stored_poison() -> i32 {
^entry:
  %p: ptr = alloca stack i32 @0
  %x: i32 = poison @0
  store nonatomic %x, %p @0
  %w: i32 = load nonatomic %p @0
  ret %w @0
}

func @at(%k: i64, %v: i8) -> i8 {
^entry:
  %p: ptr = alloca stack i8 8 align(4) @0
  %q: ptr = ptradd %p, %k @0
  store nonatomic %v, %q @0
  %w: i8 = load nonatomic %q @0
  ret %w @0
}

func @misaligned(%v: i32) -> i32 {
^entry:
  %p: ptr = alloca stack i8 16 @0
  store nonatomic %v, %p @0
  ret %v @0
}

func @aligned(%v: i32) -> i32 {
^entry:
  %p: ptr = alloca stack i8 16 align(4) @0
  store nonatomic %v, %p @0
  %w: i32 = load nonatomic %p @0
  ret %w @0
}

func @promised(%k: i64, %v: i32) -> i32 {
^entry:
  %p: ptr = alloca stack i8 16 @0
  %q: ptr = ptradd %p, %k @0
  store nonatomic align(1) %v, %q @0
  %w: i32 = load nonatomic align(1) %q @0
  ret %w @0
}

func @widest_align(%v: i64) -> i64 {
^entry:
  %p: ptr = alloca stack i64 align(8388608) @0
  store nonatomic align(8388608) %v, %p @0
  %w: i64 = load nonatomic align(8388608) %p @0
  ret %w @0
}

func @escape() -> ptr {
^entry:
  %p: ptr = alloca stack i32 @0
  ret %p @0
}

func @freed(%v: i32) -> i32 {
^entry:
  %p: ptr = call @escape @0
  store nonatomic %v, %p @0
  ret %v @0
}

func @through(%p: ptr, %v: i16) -> i16 {
^entry:
  store nonatomic %v, %p @0
  ret %v @0
}

locs {
  @0 = unknown
}
