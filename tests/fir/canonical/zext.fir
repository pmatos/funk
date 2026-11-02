func @zext_i1_to_i8(%a: i1) -> i8 {
^entry:
  %r: i8 = zext %a @0
  ret %r @0
}

func @zext_i1_to_i16(%a: i1) -> i16 {
^entry:
  %r: i16 = zext %a @0
  ret %r @0
}

func @zext_i1_to_i32(%a: i1) -> i32 {
^entry:
  %r: i32 = zext %a @0
  ret %r @0
}

func @zext_i1_to_i64(%a: i1) -> i64 {
^entry:
  %r: i64 = zext %a @0
  ret %r @0
}

func @zext_i8_to_i16(%a: i8) -> i16 {
^entry:
  %r: i16 = zext %a @0
  ret %r @0
}

func @zext_i8_to_i32(%a: i8) -> i32 {
^entry:
  %r: i32 = zext %a @0
  ret %r @0
}

func @zext_i8_to_i64(%a: i8) -> i64 {
^entry:
  %r: i64 = zext %a @0
  ret %r @0
}

func @zext_i16_to_i32(%a: i16) -> i32 {
^entry:
  %r: i32 = zext %a @0
  ret %r @0
}

func @zext_i16_to_i64(%a: i16) -> i64 {
^entry:
  %r: i64 = zext %a @0
  ret %r @0
}

func @zext_i32_to_i64(%a: i32) -> i64 {
^entry:
  %r: i64 = zext %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
