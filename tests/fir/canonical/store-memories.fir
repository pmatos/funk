layout memory(1, unit(16), pointer(32), little)

func @two_units(%v: i32) -> i32 {
^entry:
  %p: ptr(1) = alloca stack i32 @0
  store nonatomic %v, %p @0
  %w: i32 = load nonatomic %p @0
  ret %w @0
}

func @low_unit(%v: i32) -> i16 {
^entry:
  %p: ptr(1) = alloca stack i32 @0
  store nonatomic %v, %p @0
  %w: i16 = load nonatomic %p @0
  ret %w @0
}

func @at(%k: i8, %v: i32) -> i32 {
^entry:
  %p: ptr(1) = alloca stack i16 4 align(2) @0
  %q: ptr(1) = ptradd %p, %k @0
  store nonatomic %v, %q @0
  %w: i32 = load nonatomic %q @0
  ret %w @0
}

func @in_each(%a: i8, %b: i8) -> i8, i8 {
^entry:
  %p: ptr = alloca stack i8 @0
  %q: ptr(1) = alloca stack i8 @0
  store nonatomic %a, %p @0
  store nonatomic %b, %q @0
  %x: i8 = load nonatomic %p @0
  %y: i8 = load nonatomic %q @0
  ret %x, %y @0
}

locs {
  @0 = unknown
}
