func @sub(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = sub %a, %b @0
  ret %r @0
}

func @sub_nuw(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = sub nuw %a, %b @0
  ret %r @0
}

func @sub_nsw(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = sub nsw %a, %b @0
  ret %r @0
}

func @sub_nuw_nsw(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = sub nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
