layout memory(1, unit(8), pointer(32), little)

func @round_trip(%x: i16) -> i16 {
^entry:
  %p: ptr(1) = alloca stack i16 2 @0
  store nonatomic %x, %p @0
  %a: i32 = ptr_expose %p @0
  %two: i32 = const 2 @0
  %b: i32 = add %a, %two @0
  %q: ptr(1) = ptr_from_int %a @0
  %r: ptr(1) = ptr_from_int %b @0
  store nonatomic %x, %r @0
  %v: i16 = load nonatomic %q @0
  %w: i16 = load nonatomic %r @0
  %s: i16 = add %v, %w @0
  ret %s @0
}

locs {
  @0 = unknown
}
