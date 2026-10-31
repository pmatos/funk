func @sub(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = sub %a, %b @0
  ret %r @0
}

func @sub_nuw(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = sub nuw %a, %b @0
  ret %r @0
}

func @sub_nsw(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = sub nsw %a, %b @0
  ret %r @0
}

func @sub_nuw_nsw(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = sub nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
