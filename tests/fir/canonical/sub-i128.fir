func @sub(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = sub %a, %b @0
  ret %r @0
}

func @sub_nuw(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = sub nuw %a, %b @0
  ret %r @0
}

func @sub_nsw(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = sub nsw %a, %b @0
  ret %r @0
}

func @sub_nuw_nsw(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = sub nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
