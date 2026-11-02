func @br(%a: i7) -> i7 {
^entry:
  br ^next(%a) @0
^next(%x: i7):
  ret %x @0
}

func @cond_br(%c: i1, %a: i7, %b: i7) -> i7 {
^entry:
  cond_br %c, ^then(%a), ^else(%b) @0
^then(%x: i7):
  ret %x @0
^else(%y: i7):
  ret %y @0
}

locs {
  @0 = unknown
}
