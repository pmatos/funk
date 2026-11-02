func @br_poison(%a: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  br ^next(%p) @0
^next(%x: i7):
  ret %x @0
}

func @cond_br_first(%c: i1, %a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  cond_br %c, ^then(%p), ^else(%b) @0
^then(%x: i7):
  ret %x @0
^else(%y: i7):
  ret %y @0
}

func @cond_br_second(%c: i1, %a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  cond_br %c, ^then(%b), ^else(%p) @0
^then(%x: i7):
  ret %x @0
^else(%y: i7):
  ret %y @0
}

func @branch_on_poison(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %c: i1 = icmp eq %p, %b @0
  cond_br %c, ^then(%b), ^else(%a) @0
^then(%x: i7):
  ret %x @0
^else(%y: i7):
  ret %y @0
}

func @branch_on_arg(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  br ^next(%p) @0
^next(%v: i7):
  %c: i1 = icmp eq %v, %b @0
  cond_br %c, ^then(%b), ^else(%a) @0
^then(%x: i7):
  ret %x @0
^else(%y: i7):
  ret %y @0
}

locs {
  @0 = unknown
}
