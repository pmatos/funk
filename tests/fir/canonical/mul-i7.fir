func @mul(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = mul %a, %b @0
  ret %r @0
}

func @mul_nuw(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = mul nuw %a, %b @0
  ret %r @0
}

func @mul_nsw(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = mul nsw %a, %b @0
  ret %r @0
}

func @mul_nuw_nsw(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = mul nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
