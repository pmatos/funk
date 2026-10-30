func @id(%x: i32) -> i32 {
^entry:
  ret %x @0
}

func @add(%a: i32, %b: i32) -> i32 {
^entry:
  %s: i32 = add %a, %b @0
  ret %s @0
}

func @double(%x: i32) -> i32 {
^entry:
  %y: i32 = add %x, %x @0
  ret %y @0
}

func @inc(%x: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %y: i32 = add %x, %one @0
  ret %y @0
}

func @const_zero() -> i32 {
^entry:
  %c: i32 = const 0 @0
  ret %c @0
}

func @const_one() -> i32 {
^entry:
  %c: i32 = const 1 @0
  ret %c @0
}

func @const_minus_one() -> i32 {
^entry:
  %c: i32 = const -1 @0
  ret %c @0
}

func @const_min() -> i32 {
^entry:
  %c: i32 = const -2147483648 @0
  ret %c @0
}

func @const_max() -> i32 {
^entry:
  %c: i32 = const 2147483647 @0
  ret %c @0
}

func @sum8(%a0: i32, %a1: i32, %a2: i32, %a3: i32, %a4: i32, %a5: i32, %a6: i32, %a7: i32) -> i32 {
^entry:
  %s1: i32 = add %a0, %a1 @0
  %s2: i32 = add %s1, %a2 @0
  %s3: i32 = add %s2, %a3 @0
  %s4: i32 = add %s3, %a4 @0
  %s5: i32 = add %s4, %a5 @0
  %s6: i32 = add %s5, %a6 @0
  %s7: i32 = add %s6, %a7 @0
  ret %s7 @0
}

func @last(%a0: i32, %a1: i32, %a2: i32, %a3: i32, %a4: i32, %a5: i32, %a6: i32, %a7: i32) -> i32 {
^entry:
  ret %a7 @0
}

func @none(%x: i32) {
^entry:
  ret @0
}

locs {
  @0 = unknown
}
