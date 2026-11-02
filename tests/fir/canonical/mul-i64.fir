func @mul(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = mul %a, %b @0
  ret %r @0
}

func @mul_nuw(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = mul nuw %a, %b @0
  ret %r @0
}

func @mul_nsw(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = mul nsw %a, %b @0
  ret %r @0
}

func @mul_nuw_nsw(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = mul nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
