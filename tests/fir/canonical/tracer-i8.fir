func @id(%x: i8) -> i8 {
^entry:
  ret %x @0
}

func @add(%a: i8, %b: i8) -> i8 {
^entry:
  %s: i8 = add %a, %b @0
  ret %s @0
}

func @double(%x: i8) -> i8 {
^entry:
  %y: i8 = add %x, %x @0
  ret %y @0
}

func @inc(%x: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %y: i8 = add %x, %one @0
  ret %y @0
}

func @const_zero() -> i8 {
^entry:
  %c: i8 = const 0 @0
  ret %c @0
}

func @const_one() -> i8 {
^entry:
  %c: i8 = const 1 @0
  ret %c @0
}

func @const_minus_one() -> i8 {
^entry:
  %c: i8 = const -1 @0
  ret %c @0
}

func @const_min() -> i8 {
^entry:
  %c: i8 = const -128 @0
  ret %c @0
}

func @const_max() -> i8 {
^entry:
  %c: i8 = const 127 @0
  ret %c @0
}

func @sum8(%a0: i8, %a1: i8, %a2: i8, %a3: i8, %a4: i8, %a5: i8, %a6: i8, %a7: i8) -> i8 {
^entry:
  %s1: i8 = add %a0, %a1 @0
  %s2: i8 = add %s1, %a2 @0
  %s3: i8 = add %s2, %a3 @0
  %s4: i8 = add %s3, %a4 @0
  %s5: i8 = add %s4, %a5 @0
  %s6: i8 = add %s5, %a6 @0
  %s7: i8 = add %s6, %a7 @0
  ret %s7 @0
}

func @last(%a0: i8, %a1: i8, %a2: i8, %a3: i8, %a4: i8, %a5: i8, %a6: i8, %a7: i8) -> i8 {
^entry:
  ret %a7 @0
}

func @none(%x: i8) {
^entry:
  ret @0
}

locs {
  @0 = unknown
}
