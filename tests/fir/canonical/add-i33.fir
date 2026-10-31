func @add(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = add %a, %b @0
  ret %r @0
}

func @add_nuw(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = add nuw %a, %b @0
  ret %r @0
}

func @add_nsw(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = add nsw %a, %b @0
  ret %r @0
}

func @add_nuw_nsw(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = add nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
