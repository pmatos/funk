func @add(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = add %a, %b @0
  ret %r @0
}

func @add_nuw(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = add nuw %a, %b @0
  ret %r @0
}

func @add_nsw(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = add nsw %a, %b @0
  ret %r @0
}

func @add_nuw_nsw(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = add nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
