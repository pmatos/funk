func @br_poison(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  br ^next(%p) @0
^next(%x: i1):
  ret %x @0
}

func @cond_br_first(%c: i1, %a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  cond_br %c, ^then(%p), ^else(%b) @0
^then(%x: i1):
  ret %x @0
^else(%y: i1):
  ret %y @0
}

func @cond_br_second(%c: i1, %a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  cond_br %c, ^then(%b), ^else(%p) @0
^then(%x: i1):
  ret %x @0
^else(%y: i1):
  ret %y @0
}

func @branch_on_poison(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %c: i1 = icmp eq %p, %b @0
  cond_br %c, ^then(%b), ^else(%a) @0
^then(%x: i1):
  ret %x @0
^else(%y: i1):
  ret %y @0
}

func @branch_on_arg(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  br ^next(%p) @0
^next(%v: i1):
  %c: i1 = icmp eq %v, %b @0
  cond_br %c, ^then(%b), ^else(%a) @0
^then(%x: i1):
  ret %x @0
^else(%y: i1):
  ret %y @0
}

locs {
  @0 = unknown
}
