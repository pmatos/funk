func @trunc_i7_to_i1(%a: i7) -> i1 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i1 = trunc %p @0
  ret %r @0
}

func @trunc_i8_to_i1(%a: i8) -> i1 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i1 = trunc %p @0
  ret %r @0
}

func @trunc_i8_to_i7(%a: i8) -> i7 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i7 = trunc %p @0
  ret %r @0
}

func @trunc_i16_to_i1(%a: i16) -> i1 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i1 = trunc %p @0
  ret %r @0
}

func @trunc_i16_to_i7(%a: i16) -> i7 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i7 = trunc %p @0
  ret %r @0
}

func @trunc_i16_to_i8(%a: i16) -> i8 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i8 = trunc %p @0
  ret %r @0
}

func @trunc_i32_to_i1(%a: i32) -> i1 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i1 = trunc %p @0
  ret %r @0
}

func @trunc_i32_to_i7(%a: i32) -> i7 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i7 = trunc %p @0
  ret %r @0
}

func @trunc_i32_to_i8(%a: i32) -> i8 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i8 = trunc %p @0
  ret %r @0
}

func @trunc_i32_to_i16(%a: i32) -> i16 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i16 = trunc %p @0
  ret %r @0
}

func @trunc_i33_to_i1(%a: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = trunc %p @0
  ret %r @0
}

func @trunc_i33_to_i7(%a: i33) -> i7 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i7 = trunc %p @0
  ret %r @0
}

func @trunc_i33_to_i8(%a: i33) -> i8 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i8 = trunc %p @0
  ret %r @0
}

func @trunc_i33_to_i16(%a: i33) -> i16 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i16 = trunc %p @0
  ret %r @0
}

func @trunc_i33_to_i32(%a: i33) -> i32 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i32 = trunc %p @0
  ret %r @0
}

func @trunc_i64_to_i1(%a: i64) -> i1 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i1 = trunc %p @0
  ret %r @0
}

func @trunc_i64_to_i7(%a: i64) -> i7 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i7 = trunc %p @0
  ret %r @0
}

func @trunc_i64_to_i8(%a: i64) -> i8 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i8 = trunc %p @0
  ret %r @0
}

func @trunc_i64_to_i16(%a: i64) -> i16 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i16 = trunc %p @0
  ret %r @0
}

func @trunc_i64_to_i32(%a: i64) -> i32 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i32 = trunc %p @0
  ret %r @0
}

func @trunc_i64_to_i33(%a: i64) -> i33 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i33 = trunc %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
