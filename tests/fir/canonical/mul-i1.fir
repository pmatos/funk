func @mul(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = mul %a, %b @0
  ret %r @0
}

func @mul_nuw(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = mul nuw %a, %b @0
  ret %r @0
}

func @mul_nsw(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = mul nsw %a, %b @0
  ret %r @0
}

func @mul_nuw_nsw(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = mul nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
