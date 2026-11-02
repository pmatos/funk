func @freeze(%a: i1) -> i1 {
^entry:
  %f: i1 = freeze %a @0
  ret %f @0
}

func @freeze_poison(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %f: i1 = freeze %p @0
  ret %f @0
}

func @freeze_sub(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %f: i1 = freeze %p @0
  %d: i1 = sub %f, %f @0
  ret %d @0
}

func @freeze_add(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %f: i1 = freeze %p @0
  %d: i1 = add %f, %f @0
  ret %d @0
}

func @freeze_twice(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %f: i1 = freeze %p @0
  %g: i1 = freeze %p @0
  %d: i1 = sub %f, %g @0
  ret %d @0
}

func @freeze_mul_zero(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %f: i1 = freeze %p @0
  %z: i1 = const false @0
  %d: i1 = mul %f, %z @0
  ret %d @0
}

func @freeze_square(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %f: i1 = freeze %p @0
  %d: i1 = mul nsw %f, %f @0
  ret %d @0
}

locs {
  @0 = unknown
}
