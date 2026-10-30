func @id(%x: i128) -> i128 {
^entry:
  ret %x @0
}

func @add(%a: i128, %b: i128) -> i128 {
^entry:
  %s: i128 = add %a, %b @0
  ret %s @0
}

func @double(%x: i128) -> i128 {
^entry:
  %y: i128 = add %x, %x @0
  ret %y @0
}

func @inc(%x: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %y: i128 = add %x, %one @0
  ret %y @0
}

func @const_zero() -> i128 {
^entry:
  %c: i128 = const 0 @0
  ret %c @0
}

func @const_one() -> i128 {
^entry:
  %c: i128 = const 1 @0
  ret %c @0
}

func @const_minus_one() -> i128 {
^entry:
  %c: i128 = const -1 @0
  ret %c @0
}

func @const_min() -> i128 {
^entry:
  %c: i128 = const -170141183460469231731687303715884105728 @0
  ret %c @0
}

func @const_max() -> i128 {
^entry:
  %c: i128 = const 170141183460469231731687303715884105727 @0
  ret %c @0
}

func @sum8(%a0: i128, %a1: i128, %a2: i128, %a3: i128, %a4: i128, %a5: i128, %a6: i128, %a7: i128) -> i128 {
^entry:
  %s1: i128 = add %a0, %a1 @0
  %s2: i128 = add %s1, %a2 @0
  %s3: i128 = add %s2, %a3 @0
  %s4: i128 = add %s3, %a4 @0
  %s5: i128 = add %s4, %a5 @0
  %s6: i128 = add %s5, %a6 @0
  %s7: i128 = add %s6, %a7 @0
  ret %s7 @0
}

func @last(%a0: i128, %a1: i128, %a2: i128, %a3: i128, %a4: i128, %a5: i128, %a6: i128, %a7: i128) -> i128 {
^entry:
  ret %a7 @0
}

func @none(%x: i128) {
^entry:
  ret @0
}

locs {
  @0 = unknown
}
