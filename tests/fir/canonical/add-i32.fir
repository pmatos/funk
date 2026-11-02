func @add(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = add %a, %b @0
  ret %r @0
}

func @add_nuw(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = add nuw %a, %b @0
  ret %r @0
}

func @add_nsw(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = add nsw %a, %b @0
  ret %r @0
}

func @add_nuw_nsw(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = add nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
