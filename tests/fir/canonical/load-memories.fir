layout memory(1, unit(16), pointer(32), little)

func @two_units() -> i32 {
^entry:
  %p: ptr(1) = alloca stack i32 @0
  %v: i32 = load nonatomic %p @0
  ret %v @0
}

func @at(%k: i8) -> i32 {
^entry:
  %p: ptr(1) = alloca stack i16 4 align(2) @0
  %q: ptr(1) = ptradd %p, %k @0
  %v: i32 = load nonatomic %q @0
  ret %v @0
}

func @in_each() -> i8 {
^entry:
  %p: ptr = alloca stack i8 @0
  %q: ptr(1) = alloca stack i8 @0
  %v: i8 = load nonatomic %q @0
  ret %v @0
}

locs {
  @0 = unknown
}
