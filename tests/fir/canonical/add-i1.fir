func @add(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = add %a, %b @0
  ret %r @0
}

func @add_nuw(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = add nuw %a, %b @0
  ret %r @0
}

func @add_nsw(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = add nsw %a, %b @0
  ret %r @0
}

func @add_nuw_nsw(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = add nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
