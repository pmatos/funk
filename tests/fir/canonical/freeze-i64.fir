func @freeze(%a: i64) -> i64 {
^entry:
  %f: i64 = freeze %a @0
  ret %f @0
}

func @freeze_poison(%a: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %f: i64 = freeze %p @0
  ret %f @0
}

func @freeze_sub(%a: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %f: i64 = freeze %p @0
  %d: i64 = sub %f, %f @0
  ret %d @0
}

func @freeze_add(%a: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %f: i64 = freeze %p @0
  %d: i64 = add %f, %f @0
  ret %d @0
}

func @freeze_twice(%a: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %f: i64 = freeze %p @0
  %g: i64 = freeze %p @0
  %d: i64 = sub %f, %g @0
  ret %d @0
}

func @freeze_mul_zero(%a: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %f: i64 = freeze %p @0
  %z: i64 = const 0 @0
  %d: i64 = mul %f, %z @0
  ret %d @0
}

func @freeze_square(%a: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %f: i64 = freeze %p @0
  %d: i64 = mul nsw %f, %f @0
  ret %d @0
}

func @freeze_double(%a: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %f: i64 = freeze %p @0
  %two: i64 = const 2 @0
  %s: i64 = add %f, %f @0
  %m: i64 = mul %f, %two @0
  %d: i64 = sub %s, %m @0
  ret %d @0
}

locs {
  @0 = unknown
}
