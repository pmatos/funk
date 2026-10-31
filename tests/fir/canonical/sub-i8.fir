func @sub(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = sub %a, %b @0
  ret %r @0
}

func @sub_nuw(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = sub nuw %a, %b @0
  ret %r @0
}

func @sub_nsw(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = sub nsw %a, %b @0
  ret %r @0
}

func @sub_nuw_nsw(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = sub nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
