layout memory(1, unit(16), pointer(32), little, align(4))

func @own_memory(%v: i16) -> i16 {
^entry:
  %x: ptr(1) = alloca stack i16 @0
  %s: ptr(1) = alloca stack ptr(1) @0
  store nonatomic %v, %x @0
  store nonatomic %x, %s @0
  %y: ptr(1) = load nonatomic %s @0
  %w: i16 = load nonatomic %y @0
  ret %w @0
}

func @default_in_one(%v: i8) -> i8 {
^entry:
  %x: ptr = alloca stack i8 @0
  %s: ptr(1) = alloca stack ptr @0
  store nonatomic %v, %x @0
  store nonatomic %x, %s @0
  %y: ptr = load nonatomic %s @0
  %w: i8 = load nonatomic %y @0
  ret %w @0
}

func @one_in_default(%v: i16) -> i16 {
^entry:
  %x: ptr(1) = alloca stack i16 @0
  %s: ptr = alloca stack ptr(1) @0
  store nonatomic %v, %x @0
  store nonatomic %x, %s @0
  %y: ptr(1) = load nonatomic %s @0
  %w: i16 = load nonatomic %y @0
  ret %w @0
}

func @wrong_memory() -> ptr {
^entry:
  %x: ptr(1) = alloca stack i16 @0
  %s: ptr = alloca stack ptr @0
  store nonatomic %x, %s @0
  %r: ptr = load nonatomic %s @0
  ret %r @0
}

func @wrong_memory_in_one() -> ptr(1) {
^entry:
  %x: ptr = alloca stack i8 @0
  %s: ptr(1) = alloca stack ptr @0
  store nonatomic %x, %s @0
  %r: ptr(1) = load nonatomic %s @0
  ret %r @0
}

func @at(%k: i8) -> ptr(1) {
^entry:
  %s: ptr(1) = alloca stack ptr(1) 4 @0
  %q: ptr(1) = ptradd %s, %k @0
  store nonatomic %s, %q @0
  %r: ptr(1) = load nonatomic %q @0
  ret %r @0
}

func @at_two(%k: i8) -> ptr(1) {
^entry:
  %s: ptr(1) = alloca stack ptr(1) 4 @0
  %q: ptr(1) = ptradd %s, %k @0
  store nonatomic align(2) %s, %q @0
  %r: ptr(1) = load nonatomic align(2) %q @0
  ret %r @0
}

locs {
  @0 = unknown
}
