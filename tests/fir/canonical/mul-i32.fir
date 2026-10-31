func @mul(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = mul %a, %b @0
  ret %r @0
}

func @mul_nuw(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = mul nuw %a, %b @0
  ret %r @0
}

func @mul_nsw(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = mul nsw %a, %b @0
  ret %r @0
}

func @mul_nuw_nsw(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = mul nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
