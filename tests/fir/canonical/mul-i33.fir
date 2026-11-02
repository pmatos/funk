func @mul(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = mul %a, %b @0
  ret %r @0
}

func @mul_nuw(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = mul nuw %a, %b @0
  ret %r @0
}

func @mul_nsw(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = mul nsw %a, %b @0
  ret %r @0
}

func @mul_nuw_nsw(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = mul nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
