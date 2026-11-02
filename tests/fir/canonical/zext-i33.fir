func @zext_i1_to_i33(%a: i1) -> i33 {
^entry:
  %r: i33 = zext %a @0
  ret %r @0
}

func @zext_i8_to_i33(%a: i8) -> i33 {
^entry:
  %r: i33 = zext %a @0
  ret %r @0
}

func @zext_i16_to_i33(%a: i16) -> i33 {
^entry:
  %r: i33 = zext %a @0
  ret %r @0
}

func @zext_i32_to_i33(%a: i32) -> i33 {
^entry:
  %r: i33 = zext %a @0
  ret %r @0
}

func @zext_i33_to_i64(%a: i33) -> i64 {
^entry:
  %r: i64 = zext %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
