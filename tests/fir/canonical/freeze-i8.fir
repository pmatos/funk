func @freeze(%a: i8) -> i8 {
^entry:
  %f: i8 = freeze %a @0
  ret %f @0
}

func @freeze_poison(%a: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %f: i8 = freeze %p @0
  ret %f @0
}

func @freeze_sub(%a: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %f: i8 = freeze %p @0
  %d: i8 = sub %f, %f @0
  ret %d @0
}

func @freeze_add(%a: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %f: i8 = freeze %p @0
  %d: i8 = add %f, %f @0
  ret %d @0
}

func @freeze_twice(%a: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %f: i8 = freeze %p @0
  %g: i8 = freeze %p @0
  %d: i8 = sub %f, %g @0
  ret %d @0
}

func @freeze_mul_zero(%a: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %f: i8 = freeze %p @0
  %z: i8 = const 0 @0
  %d: i8 = mul %f, %z @0
  ret %d @0
}

func @freeze_square(%a: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %f: i8 = freeze %p @0
  %d: i8 = mul nsw %f, %f @0
  ret %d @0
}

func @freeze_double(%a: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %f: i8 = freeze %p @0
  %two: i8 = const 2 @0
  %s: i8 = add %f, %f @0
  %m: i8 = mul %f, %two @0
  %d: i8 = sub %s, %m @0
  ret %d @0
}

locs {
  @0 = unknown
}
