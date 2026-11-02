func @br(%a: i1) -> i1 {
^entry:
  br ^next(%a) @0
^next(%x: i1):
  ret %x @0
}

func @cond_br(%c: i1, %a: i1, %b: i1) -> i1 {
^entry:
  cond_br %c, ^then(%a), ^else(%b) @0
^then(%x: i1):
  ret %x @0
^else(%y: i1):
  ret %y @0
}

locs {
  @0 = unknown
}
