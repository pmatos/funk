func @sub(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = sub %a, %b @0
  ret %r @0
}

func @sub_nuw(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = sub nuw %a, %b @0
  ret %r @0
}

func @sub_nsw(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = sub nsw %a, %b @0
  ret %r @0
}

func @sub_nuw_nsw(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = sub nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
