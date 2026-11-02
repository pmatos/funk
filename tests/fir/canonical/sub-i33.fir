func @sub(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = sub %a, %b @0
  ret %r @0
}

func @sub_nuw(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = sub nuw %a, %b @0
  ret %r @0
}

func @sub_nsw(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = sub nsw %a, %b @0
  ret %r @0
}

func @sub_nuw_nsw(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = sub nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
