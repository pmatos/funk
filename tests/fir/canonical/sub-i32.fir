func @sub(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = sub %a, %b @0
  ret %r @0
}

func @sub_nuw(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = sub nuw %a, %b @0
  ret %r @0
}

func @sub_nsw(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = sub nsw %a, %b @0
  ret %r @0
}

func @sub_nuw_nsw(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = sub nuw nsw %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
