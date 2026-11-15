func @round_trip(%v: i32) -> i32 {
^entry:
  %p: ptr = alloca stack i32 @0
  store nonatomic %v, %p @0
  %w: i32 = load nonatomic %p @0
  ret %w @0
}

func @widths(%a: i1, %b: i7, %c: i8, %d: i16, %e: i33, %f: i64, %g: i128) -> i1, i7, i8, i16, i33, i64, i128 {
^entry:
  %pa: ptr = alloca stack i1 @0
  %pb: ptr = alloca stack i7 @0
  %pc: ptr = alloca stack i8 @0
  %pd: ptr = alloca stack i16 @0
  %pe: ptr = alloca stack i33 @0
  %pf: ptr = alloca stack i64 @0
  %pg: ptr = alloca stack i128 @0
  store nonatomic %a, %pa @0
  store nonatomic %b, %pb @0
  store nonatomic %c, %pc @0
  store nonatomic %d, %pd @0
  store nonatomic %e, %pe @0
  store nonatomic %f, %pf @0
  store nonatomic %g, %pg @0
  %ra: i1 = load nonatomic %pa @0
  %rb: i7 = load nonatomic %pb @0
  %rc: i8 = load nonatomic %pc @0
  %rd: i16 = load nonatomic %pd @0
  %re: i33 = load nonatomic %pe @0
  %rf: i64 = load nonatomic %pf @0
  %rg: i128 = load nonatomic %pg @0
  ret %ra, %rb, %rc, %rd, %re, %rf, %rg @0
}

func @padding(%v: i1) -> i8 {
^entry:
  %p: ptr = alloca stack i8 @0
  store nonatomic %v, %p @0
  %w: i8 = load nonatomic %p @0
  ret %w @0
}

func @padding_wide(%v: i20) -> i24 {
^entry:
  %p: ptr = alloca stack i32 @0
  store nonatomic %v, %p @0
  %w: i24 = load nonatomic %p @0
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
