func @trunc_i8_to_i1(%a: i8) -> i1 {
^entry:
  %r: i1 = trunc %a @0
  ret %r @0
}

func @trunc_i16_to_i1(%a: i16) -> i1 {
^entry:
  %r: i1 = trunc %a @0
  ret %r @0
}

func @trunc_i16_to_i8(%a: i16) -> i8 {
^entry:
  %r: i8 = trunc %a @0
  ret %r @0
}

func @trunc_i32_to_i1(%a: i32) -> i1 {
^entry:
  %r: i1 = trunc %a @0
  ret %r @0
}

func @trunc_i32_to_i8(%a: i32) -> i8 {
^entry:
  %r: i8 = trunc %a @0
  ret %r @0
}

func @trunc_i32_to_i16(%a: i32) -> i16 {
^entry:
  %r: i16 = trunc %a @0
  ret %r @0
}

func @trunc_i64_to_i1(%a: i64) -> i1 {
^entry:
  %r: i1 = trunc %a @0
  ret %r @0
}

func @trunc_i64_to_i8(%a: i64) -> i8 {
^entry:
  %r: i8 = trunc %a @0
  ret %r @0
}

func @trunc_i64_to_i16(%a: i64) -> i16 {
^entry:
  %r: i16 = trunc %a @0
  ret %r @0
}

func @trunc_i64_to_i32(%a: i64) -> i32 {
^entry:
  %r: i32 = trunc %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
