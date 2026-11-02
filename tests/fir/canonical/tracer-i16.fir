func @id(%x: i16) -> i16 {
^entry:
  ret %x @0
}

func @add(%a: i16, %b: i16) -> i16 {
^entry:
  %s: i16 = add %a, %b @0
  ret %s @0
}

func @double(%x: i16) -> i16 {
^entry:
  %y: i16 = add %x, %x @0
  ret %y @0
}

func @inc(%x: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %y: i16 = add %x, %one @0
  ret %y @0
}

func @const_zero() -> i16 {
^entry:
  %c: i16 = const 0 @0
  ret %c @0
}

func @const_one() -> i16 {
^entry:
  %c: i16 = const 1 @0
  ret %c @0
}

func @const_minus_one() -> i16 {
^entry:
  %c: i16 = const -1 @0
  ret %c @0
}

func @const_min() -> i16 {
^entry:
  %c: i16 = const -32768 @0
  ret %c @0
}

func @const_max() -> i16 {
^entry:
  %c: i16 = const 32767 @0
  ret %c @0
}

func @sum8(%a0: i16, %a1: i16, %a2: i16, %a3: i16, %a4: i16, %a5: i16, %a6: i16, %a7: i16) -> i16 {
^entry:
  %s1: i16 = add %a0, %a1 @0
  %s2: i16 = add %s1, %a2 @0
  %s3: i16 = add %s2, %a3 @0
  %s4: i16 = add %s3, %a4 @0
  %s5: i16 = add %s4, %a5 @0
  %s6: i16 = add %s5, %a6 @0
  %s7: i16 = add %s6, %a7 @0
  ret %s7 @0
}

func @last(%a0: i16, %a1: i16, %a2: i16, %a3: i16, %a4: i16, %a5: i16, %a6: i16, %a7: i16) -> i16 {
^entry:
  ret %a7 @0
}

func @none(%x: i16) {
^entry:
  ret @0
}

locs {
  @0 = unknown
}
