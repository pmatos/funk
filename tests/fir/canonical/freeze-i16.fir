func @freeze(%a: i16) -> i16 {
^entry:
  %f: i16 = freeze %a @0
  ret %f @0
}

func @freeze_poison(%a: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %f: i16 = freeze %p @0
  ret %f @0
}

func @freeze_sub(%a: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %f: i16 = freeze %p @0
  %d: i16 = sub %f, %f @0
  ret %d @0
}

func @freeze_add(%a: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %f: i16 = freeze %p @0
  %d: i16 = add %f, %f @0
  ret %d @0
}

func @freeze_twice(%a: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %f: i16 = freeze %p @0
  %g: i16 = freeze %p @0
  %d: i16 = sub %f, %g @0
  ret %d @0
}

func @freeze_mul_zero(%a: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %f: i16 = freeze %p @0
  %z: i16 = const 0 @0
  %d: i16 = mul %f, %z @0
  ret %d @0
}

func @freeze_square(%a: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %f: i16 = freeze %p @0
  %d: i16 = mul nsw %f, %f @0
  ret %d @0
}

func @freeze_double(%a: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %f: i16 = freeze %p @0
  %two: i16 = const 2 @0
  %s: i16 = add %f, %f @0
  %m: i16 = mul %f, %two @0
  %d: i16 = sub %s, %m @0
  ret %d @0
}

locs {
  @0 = unknown
}
