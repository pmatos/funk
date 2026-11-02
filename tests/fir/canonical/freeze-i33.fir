func @freeze(%a: i33) -> i33 {
^entry:
  %f: i33 = freeze %a @0
  ret %f @0
}

func @freeze_poison(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %f: i33 = freeze %p @0
  ret %f @0
}

func @freeze_sub(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %f: i33 = freeze %p @0
  %d: i33 = sub %f, %f @0
  ret %d @0
}

func @freeze_add(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %f: i33 = freeze %p @0
  %d: i33 = add %f, %f @0
  ret %d @0
}

func @freeze_twice(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %f: i33 = freeze %p @0
  %g: i33 = freeze %p @0
  %d: i33 = sub %f, %g @0
  ret %d @0
}

func @freeze_mul_zero(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %f: i33 = freeze %p @0
  %z: i33 = const 0 @0
  %d: i33 = mul %f, %z @0
  ret %d @0
}

func @freeze_square(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %f: i33 = freeze %p @0
  %d: i33 = mul nsw %f, %f @0
  ret %d @0
}

func @freeze_double(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %f: i33 = freeze %p @0
  %two: i33 = const 2 @0
  %s: i33 = add %f, %f @0
  %m: i33 = mul %f, %two @0
  %d: i33 = sub %s, %m @0
  ret %d @0
}

locs {
  @0 = unknown
}
