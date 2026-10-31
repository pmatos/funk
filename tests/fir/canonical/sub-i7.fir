func @sub(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = sub %a, %b @0
  ret %r @0
}

func @sub_nuw(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = sub nuw %a, %b @0
  ret %r @0
}

func @sub_nsw(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = sub nsw %a, %b @0
  ret %r @0
}

func @sub_nuw_nsw(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = sub nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
