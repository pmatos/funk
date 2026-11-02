func @freeze(%a: i7) -> i7 {
^entry:
  %f: i7 = freeze %a @0
  ret %f @0
}

func @freeze_poison(%a: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %f: i7 = freeze %p @0
  ret %f @0
}

func @freeze_sub(%a: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %f: i7 = freeze %p @0
  %d: i7 = sub %f, %f @0
  ret %d @0
}

func @freeze_add(%a: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %f: i7 = freeze %p @0
  %d: i7 = add %f, %f @0
  ret %d @0
}

func @freeze_twice(%a: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %f: i7 = freeze %p @0
  %g: i7 = freeze %p @0
  %d: i7 = sub %f, %g @0
  ret %d @0
}

func @freeze_mul_zero(%a: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %f: i7 = freeze %p @0
  %z: i7 = const 0 @0
  %d: i7 = mul %f, %z @0
  ret %d @0
}

func @freeze_square(%a: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %f: i7 = freeze %p @0
  %d: i7 = mul nsw %f, %f @0
  ret %d @0
}

func @freeze_double(%a: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %f: i7 = freeze %p @0
  %two: i7 = const 2 @0
  %s: i7 = add %f, %f @0
  %m: i7 = mul %f, %two @0
  %d: i7 = sub %s, %m @0
  ret %d @0
}

locs {
  @0 = unknown
}
