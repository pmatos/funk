func @trunc_i33_to_i1(%a: i33) -> i1 {
^entry:
  %r: i1 = trunc %a @0
  ret %r @0
}

func @trunc_i33_to_i8(%a: i33) -> i8 {
^entry:
  %r: i8 = trunc %a @0
  ret %r @0
}

func @trunc_i33_to_i16(%a: i33) -> i16 {
^entry:
  %r: i16 = trunc %a @0
  ret %r @0
}

func @trunc_i33_to_i32(%a: i33) -> i32 {
^entry:
  %r: i32 = trunc %a @0
  ret %r @0
}

func @trunc_i64_to_i33(%a: i64) -> i33 {
^entry:
  %r: i33 = trunc %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
