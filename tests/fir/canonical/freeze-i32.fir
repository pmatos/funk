func @freeze(%a: i32) -> i32 {
^entry:
  %f: i32 = freeze %a @0
  ret %f @0
}

func @freeze_poison(%a: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %f: i32 = freeze %p @0
  ret %f @0
}

func @freeze_sub(%a: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %f: i32 = freeze %p @0
  %d: i32 = sub %f, %f @0
  ret %d @0
}

func @freeze_add(%a: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %f: i32 = freeze %p @0
  %d: i32 = add %f, %f @0
  ret %d @0
}

func @freeze_twice(%a: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %f: i32 = freeze %p @0
  %g: i32 = freeze %p @0
  %d: i32 = sub %f, %g @0
  ret %d @0
}

func @freeze_mul_zero(%a: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %f: i32 = freeze %p @0
  %z: i32 = const 0 @0
  %d: i32 = mul %f, %z @0
  ret %d @0
}

func @freeze_square(%a: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %f: i32 = freeze %p @0
  %d: i32 = mul nsw %f, %f @0
  ret %d @0
}

func @freeze_double(%a: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %f: i32 = freeze %p @0
  %two: i32 = const 2 @0
  %s: i32 = add %f, %f @0
  %m: i32 = mul %f, %two @0
  %d: i32 = sub %s, %m @0
  ret %d @0
}

locs {
  @0 = unknown
}
