func @trunc_i7_to_i1(%a: i7) -> i1 {
^entry:
  %r: i1 = trunc %a @0
  ret %r @0
}

func @trunc_i8_to_i7(%a: i8) -> i7 {
^entry:
  %r: i7 = trunc %a @0
  ret %r @0
}

func @trunc_i16_to_i7(%a: i16) -> i7 {
^entry:
  %r: i7 = trunc %a @0
  ret %r @0
}

func @trunc_i32_to_i7(%a: i32) -> i7 {
^entry:
  %r: i7 = trunc %a @0
  ret %r @0
}

func @trunc_i33_to_i7(%a: i33) -> i7 {
^entry:
  %r: i7 = trunc %a @0
  ret %r @0
}

func @trunc_i64_to_i7(%a: i64) -> i7 {
^entry:
  %r: i7 = trunc %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
