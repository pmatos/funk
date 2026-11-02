func @mul(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = mul %a, %b @0
  ret %r @0
}

func @mul_nuw(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = mul nuw %a, %b @0
  ret %r @0
}

func @mul_nsw(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = mul nsw %a, %b @0
  ret %r @0
}

func @mul_nuw_nsw(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = mul nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
