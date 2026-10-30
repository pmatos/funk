func @id(%x: i7) -> i7 {
^entry:
  ret %x @0
}

func @add(%a: i7, %b: i7) -> i7 {
^entry:
  %s: i7 = add %a, %b @0
  ret %s @0
}

func @double(%x: i7) -> i7 {
^entry:
  %y: i7 = add %x, %x @0
  ret %y @0
}

func @inc(%x: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %y: i7 = add %x, %one @0
  ret %y @0
}

func @const_zero() -> i7 {
^entry:
  %c: i7 = const 0 @0
  ret %c @0
}

func @const_one() -> i7 {
^entry:
  %c: i7 = const 1 @0
  ret %c @0
}

func @const_minus_one() -> i7 {
^entry:
  %c: i7 = const -1 @0
  ret %c @0
}

func @const_min() -> i7 {
^entry:
  %c: i7 = const -64 @0
  ret %c @0
}

func @const_max() -> i7 {
^entry:
  %c: i7 = const 63 @0
  ret %c @0
}

func @sum8(%a0: i7, %a1: i7, %a2: i7, %a3: i7, %a4: i7, %a5: i7, %a6: i7, %a7: i7) -> i7 {
^entry:
  %s1: i7 = add %a0, %a1 @0
  %s2: i7 = add %s1, %a2 @0
  %s3: i7 = add %s2, %a3 @0
  %s4: i7 = add %s3, %a4 @0
  %s5: i7 = add %s4, %a5 @0
  %s6: i7 = add %s5, %a6 @0
  %s7: i7 = add %s6, %a7 @0
  ret %s7 @0
}

func @last(%a0: i7, %a1: i7, %a2: i7, %a3: i7, %a4: i7, %a5: i7, %a6: i7, %a7: i7) -> i7 {
^entry:
  ret %a7 @0
}

func @none(%x: i7) {
^entry:
  ret @0
}

locs {
  @0 = unknown
}
