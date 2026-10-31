func @zext_i1_to_i7(%a: i1) -> i7 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i7 = zext %p @0
  ret %r @0
}

func @zext_i1_to_i8(%a: i1) -> i8 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i8 = zext %p @0
  ret %r @0
}

func @zext_i1_to_i16(%a: i1) -> i16 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i16 = zext %p @0
  ret %r @0
}

func @zext_i1_to_i32(%a: i1) -> i32 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i32 = zext %p @0
  ret %r @0
}

func @zext_i1_to_i33(%a: i1) -> i33 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i33 = zext %p @0
  ret %r @0
}

func @zext_i1_to_i64(%a: i1) -> i64 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i64 = zext %p @0
  ret %r @0
}

func @zext_i7_to_i8(%a: i7) -> i8 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i8 = zext %p @0
  ret %r @0
}

func @zext_i7_to_i16(%a: i7) -> i16 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i16 = zext %p @0
  ret %r @0
}

func @zext_i7_to_i32(%a: i7) -> i32 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i32 = zext %p @0
  ret %r @0
}

func @zext_i7_to_i33(%a: i7) -> i33 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i33 = zext %p @0
  ret %r @0
}

func @zext_i7_to_i64(%a: i7) -> i64 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i64 = zext %p @0
  ret %r @0
}

func @zext_i8_to_i16(%a: i8) -> i16 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i16 = zext %p @0
  ret %r @0
}

func @zext_i8_to_i32(%a: i8) -> i32 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i32 = zext %p @0
  ret %r @0
}

func @zext_i8_to_i33(%a: i8) -> i33 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i33 = zext %p @0
  ret %r @0
}

func @zext_i8_to_i64(%a: i8) -> i64 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i64 = zext %p @0
  ret %r @0
}

func @zext_i16_to_i32(%a: i16) -> i32 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i32 = zext %p @0
  ret %r @0
}

func @zext_i16_to_i33(%a: i16) -> i33 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i33 = zext %p @0
  ret %r @0
}

func @zext_i16_to_i64(%a: i16) -> i64 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i64 = zext %p @0
  ret %r @0
}

func @zext_i32_to_i33(%a: i32) -> i33 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i33 = zext %p @0
  ret %r @0
}

func @zext_i32_to_i64(%a: i32) -> i64 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i64 = zext %p @0
  ret %r @0
}

func @zext_i33_to_i64(%a: i33) -> i64 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i64 = zext %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
