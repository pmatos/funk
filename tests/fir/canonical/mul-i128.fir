func @mul(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = mul %a, %b @0
  ret %r @0
}

func @mul_nuw(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = mul nuw %a, %b @0
  ret %r @0
}

func @mul_nsw(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = mul nsw %a, %b @0
  ret %r @0
}

func @mul_nuw_nsw(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = mul nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
