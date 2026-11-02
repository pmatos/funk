func @id(%x: i64) -> i64 {
^entry:
  ret %x @0
}

func @add(%a: i64, %b: i64) -> i64 {
^entry:
  %s: i64 = add %a, %b @0
  ret %s @0
}

func @double(%x: i64) -> i64 {
^entry:
  %y: i64 = add %x, %x @0
  ret %y @0
}

func @inc(%x: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %y: i64 = add %x, %one @0
  ret %y @0
}

func @const_zero() -> i64 {
^entry:
  %c: i64 = const 0 @0
  ret %c @0
}

func @const_one() -> i64 {
^entry:
  %c: i64 = const 1 @0
  ret %c @0
}

func @const_minus_one() -> i64 {
^entry:
  %c: i64 = const -1 @0
  ret %c @0
}

func @const_min() -> i64 {
^entry:
  %c: i64 = const -9223372036854775808 @0
  ret %c @0
}

func @const_max() -> i64 {
^entry:
  %c: i64 = const 9223372036854775807 @0
  ret %c @0
}

func @sum8(%a0: i64, %a1: i64, %a2: i64, %a3: i64, %a4: i64, %a5: i64, %a6: i64, %a7: i64) -> i64 {
^entry:
  %s1: i64 = add %a0, %a1 @0
  %s2: i64 = add %s1, %a2 @0
  %s3: i64 = add %s2, %a3 @0
  %s4: i64 = add %s3, %a4 @0
  %s5: i64 = add %s4, %a5 @0
  %s6: i64 = add %s5, %a6 @0
  %s7: i64 = add %s6, %a7 @0
  ret %s7 @0
}

func @last(%a0: i64, %a1: i64, %a2: i64, %a3: i64, %a4: i64, %a5: i64, %a6: i64, %a7: i64) -> i64 {
^entry:
  ret %a7 @0
}

func @none(%x: i64) {
^entry:
  ret @0
}

locs {
  @0 = unknown
}
