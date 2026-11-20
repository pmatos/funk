layout memory(1, unit(16), pointer(32), little)

func @fill(%v: i16, %n: i16) -> i32 {
^entry:
  %p: ptr(1) = alloca stack i32 @0
  %x: i32 = const 67305985 @0
  store nonatomic %x, %p @0
  memset nonatomic %p, %v, %n @0
  %w: i32 = load nonatomic %p @0
  ret %w @0
}

func @past(%n: i32) -> i32 {
^entry:
  %p: ptr(1) = alloca stack i32 @1
  %v: i16 = const 1 @1
  memset nonatomic %p, %v, %n @1
  ret %n @1
}

locs {
  @0 = unknown
  @1 = unknown
}
