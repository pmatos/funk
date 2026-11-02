func @id(%x: i33) -> i33 {
^entry:
  ret %x @0
}

func @add(%a: i33, %b: i33) -> i33 {
^entry:
  %s: i33 = add %a, %b @0
  ret %s @0
}

func @double(%x: i33) -> i33 {
^entry:
  %y: i33 = add %x, %x @0
  ret %y @0
}

func @inc(%x: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %y: i33 = add %x, %one @0
  ret %y @0
}

func @const_zero() -> i33 {
^entry:
  %c: i33 = const 0 @0
  ret %c @0
}

func @const_one() -> i33 {
^entry:
  %c: i33 = const 1 @0
  ret %c @0
}

func @const_minus_one() -> i33 {
^entry:
  %c: i33 = const -1 @0
  ret %c @0
}

func @const_min() -> i33 {
^entry:
  %c: i33 = const -4294967296 @0
  ret %c @0
}

func @const_max() -> i33 {
^entry:
  %c: i33 = const 4294967295 @0
  ret %c @0
}

func @sum8(%a0: i33, %a1: i33, %a2: i33, %a3: i33, %a4: i33, %a5: i33, %a6: i33, %a7: i33) -> i33 {
^entry:
  %s1: i33 = add %a0, %a1 @0
  %s2: i33 = add %s1, %a2 @0
  %s3: i33 = add %s2, %a3 @0
  %s4: i33 = add %s3, %a4 @0
  %s5: i33 = add %s4, %a5 @0
  %s6: i33 = add %s5, %a6 @0
  %s7: i33 = add %s6, %a7 @0
  ret %s7 @0
}

func @last(%a0: i33, %a1: i33, %a2: i33, %a3: i33, %a4: i33, %a5: i33, %a6: i33, %a7: i33) -> i33 {
^entry:
  ret %a7 @0
}

func @none(%x: i33) {
^entry:
  ret @0
}

locs {
  @0 = unknown
}
