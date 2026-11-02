func @add_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = add %p, %b @0
  ret %r @0
}

func @add_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = add %b, %p @0
  ret %r @0
}

func @add_nuw_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = add nuw %p, %b @0
  ret %r @0
}

func @add_nuw_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = add nuw %b, %p @0
  ret %r @0
}

func @add_nsw_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = add nsw %p, %b @0
  ret %r @0
}

func @add_nsw_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = add nsw %b, %p @0
  ret %r @0
}

func @add_nuw_nsw_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = add nuw nsw %p, %b @0
  ret %r @0
}

func @add_nuw_nsw_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = add nuw nsw %b, %p @0
  ret %r @0
}

func @sub_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = sub %p, %b @0
  ret %r @0
}

func @sub_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = sub %b, %p @0
  ret %r @0
}

func @sub_nuw_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = sub nuw %p, %b @0
  ret %r @0
}

func @sub_nuw_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = sub nuw %b, %p @0
  ret %r @0
}

func @sub_nsw_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = sub nsw %p, %b @0
  ret %r @0
}

func @sub_nsw_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = sub nsw %b, %p @0
  ret %r @0
}

func @sub_nuw_nsw_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = sub nuw nsw %p, %b @0
  ret %r @0
}

func @sub_nuw_nsw_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = sub nuw nsw %b, %p @0
  ret %r @0
}

func @mul_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = mul %p, %b @0
  ret %r @0
}

func @mul_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = mul %b, %p @0
  ret %r @0
}

func @mul_nuw_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = mul nuw %p, %b @0
  ret %r @0
}

func @mul_nuw_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = mul nuw %b, %p @0
  ret %r @0
}

func @mul_nsw_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = mul nsw %p, %b @0
  ret %r @0
}

func @mul_nsw_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = mul nsw %b, %p @0
  ret %r @0
}

func @mul_nuw_nsw_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = mul nuw nsw %p, %b @0
  ret %r @0
}

func @mul_nuw_nsw_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = mul nuw nsw %b, %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
