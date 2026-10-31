func @add(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = add %a, %b @0
  ret %r @0
}

func @add_nuw(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = add nuw %a, %b @0
  ret %r @0
}

func @add_nsw(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = add nsw %a, %b @0
  ret %r @0
}

func @add_nuw_nsw(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = add nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
