func @mul(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = mul %a, %b @0
  ret %r @0
}

func @mul_nuw(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = mul nuw %a, %b @0
  ret %r @0
}

func @mul_nsw(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = mul nsw %a, %b @0
  ret %r @0
}

func @mul_nuw_nsw(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = mul nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
