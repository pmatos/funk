func @br(%a: i8) -> i8 {
^entry:
  br ^next(%a) @0
^next(%x: i8):
  ret %x @0
}

func @cond_br(%c: i1, %a: i8, %b: i8) -> i8 {
^entry:
  cond_br %c, ^then(%a), ^else(%b) @0
^then(%x: i8):
  ret %x @0
^else(%y: i8):
  ret %y @0
}

locs {
  @0 = unknown
}
