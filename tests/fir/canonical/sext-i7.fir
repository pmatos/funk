func @sext_i1_to_i7(%a: i1) -> i7 {
^entry:
  %r: i7 = sext %a @0
  ret %r @0
}

func @sext_i7_to_i8(%a: i7) -> i8 {
^entry:
  %r: i8 = sext %a @0
  ret %r @0
}

func @sext_i7_to_i16(%a: i7) -> i16 {
^entry:
  %r: i16 = sext %a @0
  ret %r @0
}

func @sext_i7_to_i32(%a: i7) -> i32 {
^entry:
  %r: i32 = sext %a @0
  ret %r @0
}

func @sext_i7_to_i33(%a: i7) -> i33 {
^entry:
  %r: i33 = sext %a @0
  ret %r @0
}

func @sext_i7_to_i64(%a: i7) -> i64 {
^entry:
  %r: i64 = sext %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
