func @sext_i1_to_i128(%a: i1) -> i128 {
^entry:
  %r: i128 = sext %a @0
  ret %r @0
}

func @sext_i8_to_i128(%a: i8) -> i128 {
^entry:
  %r: i128 = sext %a @0
  ret %r @0
}

func @sext_i16_to_i128(%a: i16) -> i128 {
^entry:
  %r: i128 = sext %a @0
  ret %r @0
}

func @sext_i32_to_i128(%a: i32) -> i128 {
^entry:
  %r: i128 = sext %a @0
  ret %r @0
}

func @sext_i64_to_i128(%a: i64) -> i128 {
^entry:
  %r: i128 = sext %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
