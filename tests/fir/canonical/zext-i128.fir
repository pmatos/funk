func @zext_i1_to_i128(%a: i1) -> i128 {
^entry:
  %r: i128 = zext %a @0
  ret %r @0
}

func @zext_i8_to_i128(%a: i8) -> i128 {
^entry:
  %r: i128 = zext %a @0
  ret %r @0
}

func @zext_i16_to_i128(%a: i16) -> i128 {
^entry:
  %r: i128 = zext %a @0
  ret %r @0
}

func @zext_i32_to_i128(%a: i32) -> i128 {
^entry:
  %r: i128 = zext %a @0
  ret %r @0
}

func @zext_i64_to_i128(%a: i64) -> i128 {
^entry:
  %r: i128 = zext %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
