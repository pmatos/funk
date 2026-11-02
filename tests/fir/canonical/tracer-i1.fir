func @id(%x: i1) -> i1 {
^entry:
  ret %x @0
}

func @add(%a: i1, %b: i1) -> i1 {
^entry:
  %s: i1 = add %a, %b @0
  ret %s @0
}

func @double(%x: i1) -> i1 {
^entry:
  %y: i1 = add %x, %x @0
  ret %y @0
}

func @inc(%x: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %y: i1 = add %x, %one @0
  ret %y @0
}

func @const_false() -> i1 {
^entry:
  %c: i1 = const false @0
  ret %c @0
}

func @const_true() -> i1 {
^entry:
  %c: i1 = const true @0
  ret %c @0
}

func @sum8(%a0: i1, %a1: i1, %a2: i1, %a3: i1, %a4: i1, %a5: i1, %a6: i1, %a7: i1) -> i1 {
^entry:
  %s1: i1 = add %a0, %a1 @0
  %s2: i1 = add %s1, %a2 @0
  %s3: i1 = add %s2, %a3 @0
  %s4: i1 = add %s3, %a4 @0
  %s5: i1 = add %s4, %a5 @0
  %s6: i1 = add %s5, %a6 @0
  %s7: i1 = add %s6, %a7 @0
  ret %s7 @0
}

func @last(%a0: i1, %a1: i1, %a2: i1, %a3: i1, %a4: i1, %a5: i1, %a6: i1, %a7: i1) -> i1 {
^entry:
  ret %a7 @0
}

func @none(%x: i1) {
^entry:
  ret @0
}

locs {
  @0 = unknown
}
