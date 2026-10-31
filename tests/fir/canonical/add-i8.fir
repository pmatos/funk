func @add(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = add %a, %b @0
  ret %r @0
}

func @add_nuw(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = add nuw %a, %b @0
  ret %r @0
}

func @add_nsw(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = add nsw %a, %b @0
  ret %r @0
}

func @add_nuw_nsw(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = add nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
