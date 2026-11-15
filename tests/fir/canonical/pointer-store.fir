func @round_trip(%v: i32) -> i32 {
^entry:
  %x: ptr = alloca stack i32 @0
  %s: ptr = alloca stack ptr @0
  store nonatomic %v, %x @0
  store nonatomic %x, %s @0
  %y: ptr = load nonatomic %s @0
  %w: i32 = load nonatomic %y @0
  ret %w @0
}

func @same_pointer(%k: i8) -> ptr {
^entry:
  %x: ptr = alloca stack i8 4 @0
  %q: ptr = ptradd %x, %k @0
  %s: ptr = alloca stack ptr 2 align(16) @0
  store nonatomic %q, %s @0
  %r: ptr = load nonatomic %s @0
  ret %r @0
}

func @chain(%v: i16) -> i16 {
^entry:
  %x: ptr = alloca stack i16 @0
  %s: ptr = alloca stack ptr @0
  %t: ptr = alloca stack ptr @0
  store nonatomic %v, %x @0
  store nonatomic %x, %s @0
  store nonatomic %s, %t @0
  %a: ptr = load nonatomic %t @0
  %b: ptr = load nonatomic %a @0
  %w: i16 = load nonatomic %b @0
  ret %w @0
}

func @fresh() -> ptr {
^entry:
  %s: ptr = alloca stack ptr @0
  %r: ptr = load nonatomic %s @0
  ret %r @0
}

func @from_bits(%v: i64) -> ptr {
^entry:
  %s: ptr = alloca stack ptr @0
  store nonatomic %v, %s @0
  %r: ptr = load nonatomic %s @0
  ret %r @0
}

func @bits_of_pointer() -> i64 {
^entry:
  %x: ptr = alloca stack i8 @0
  %s: ptr = alloca stack ptr @0
  store nonatomic %x, %s @0
  %w: i64 = load nonatomic %s @0
  ret %w @0
}

func @byte_of_pointer(%k: i8) -> i8 {
^entry:
  %x: ptr = alloca stack i8 @0
  %s: ptr = alloca stack ptr @0
  store nonatomic %x, %s @0
  %q: ptr = ptradd %s, %k @0
  %w: i8 = load nonatomic %q @0
  ret %w @0
}

func @overwritten(%k: i8, %b: i8) -> ptr {
^entry:
  %x: ptr = alloca stack i8 @0
  %s: ptr = alloca stack ptr @0
  store nonatomic %x, %s @0
  %q: ptr = ptradd %s, %k @0
  store nonatomic %b, %q @0
  %r: ptr = load nonatomic %s @0
  ret %r @0
}

func @integer_copy() -> ptr {
^entry:
  %x: ptr = alloca stack i8 @0
  %s: ptr = alloca stack ptr @0
  %t: ptr = alloca stack ptr @0
  store nonatomic %x, %s @0
  %w: i64 = load nonatomic %s @0
  store nonatomic %w, %t @0
  %r: ptr = load nonatomic %t @0
  ret %r @0
}

func @pointer_copy(%v: i32) -> i32 {
^entry:
  %x: ptr = alloca stack i32 @0
  %s: ptr = alloca stack ptr @0
  %t: ptr = alloca stack ptr @0
  store nonatomic %v, %x @0
  store nonatomic %x, %s @0
  %c: ptr = load nonatomic %s @0
  store nonatomic %c, %t @0
  %y: ptr = load nonatomic %t @0
  %w: i32 = load nonatomic %y @0
  ret %w @0
}

func @stored_poison(%p: ptr) -> ptr {
^entry:
  %s: ptr = alloca stack ptr @0
  store nonatomic %p, %s @0
  %r: ptr = load nonatomic %s @0
  ret %r @0
}

func @through_poison(%p: ptr) -> ptr {
^entry:
  %r: ptr = load nonatomic %p @0
  ret %r @0
}

func @store_through_poison(%p: ptr) -> i8 {
^entry:
  %x: ptr = alloca stack i8 @0
  store nonatomic %x, %p @0
  %w: i8 = load nonatomic %x @0
  ret %w @0
}

func @at(%k: i8) -> ptr {
^entry:
  %s: ptr = alloca stack ptr 2 @0
  %q: ptr = ptradd %s, %k @0
  store nonatomic %s, %q @0
  %r: ptr = load nonatomic %q @0
  ret %r @0
}

func @at_four(%k: i8) -> ptr {
^entry:
  %s: ptr = alloca stack ptr 2 @0
  %q: ptr = ptradd %s, %k @0
  store nonatomic align(4) %s, %q @0
  %r: ptr = load nonatomic align(4) %q @0
  ret %r @0
}

func @in_bytes() -> ptr {
^entry:
  %s: ptr = alloca stack i8 8 @0
  %x: ptr = alloca stack i8 @0
  store nonatomic %x, %s @0
  %r: ptr = load nonatomic %s @0
  ret %r @0
}

func @slot() -> ptr {
^entry:
  %s: ptr = alloca stack ptr @0
  ret %s @0
}

func @freed() -> ptr {
^entry:
  %s: ptr = call @slot @0
  %r: ptr = load nonatomic %s @0
  ret %r @0
}

locs {
  @0 = unknown
}
