func @add(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = add %a, %b @0
  ret %r @0
}

func @add_nuw(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = add nuw %a, %b @0
  ret %r @0
}

func @add_nsw(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = add nsw %a, %b @0
  ret %r @0
}

func @add_nuw_nsw(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = add nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
