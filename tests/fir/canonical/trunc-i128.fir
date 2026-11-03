func @trunc_i128_to_i1(%a: i128) -> i1 {
^entry:
  %r: i1 = trunc %a @0
  ret %r @0
}

func @trunc_i128_to_i8(%a: i128) -> i8 {
^entry:
  %r: i8 = trunc %a @0
  ret %r @0
}

func @trunc_i128_to_i16(%a: i128) -> i16 {
^entry:
  %r: i16 = trunc %a @0
  ret %r @0
}

func @trunc_i128_to_i32(%a: i128) -> i32 {
^entry:
  %r: i32 = trunc %a @0
  ret %r @0
}

func @trunc_i128_to_i64(%a: i128) -> i64 {
^entry:
  %r: i64 = trunc %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
