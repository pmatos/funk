layout memory(1, unit(16), pointer(32), little), memory(2, unit(32), pointer(64), little, align(2))

func @in_one() -> ptr(1) {
^entry:
  %p: ptr(1) = alloca stack i24 5 @0
  ret %p @0
}

func @in_each() -> ptr(2) {
^entry:
  %p: ptr = alloca stack i64 @0
  %q: ptr(1) = alloca stack i8 align(8) @0
  %r: ptr(2) = alloca stack i128 @0
  ret %r @0
}

func @second_in_one() -> ptr(1) {
^entry:
  %p: ptr(1) = alloca stack i32 @0
  %q: ptr = alloca stack i32 @0
  %r: ptr(1) = alloca stack i32 2 @0
  ret %r @0
}

locs {
  @0 = unknown
}
