func @add(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = add %a, %b @0
  ret %r @0
}

func @add_nuw(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = add nuw %a, %b @0
  ret %r @0
}

func @add_nsw(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = add nsw %a, %b @0
  ret %r @0
}

func @add_nuw_nsw(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = add nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
