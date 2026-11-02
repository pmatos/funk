func @br(%a: i16) -> i16 {
^entry:
  br ^next(%a) @0
^next(%x: i16):
  ret %x @0
}

func @cond_br(%c: i1, %a: i16, %b: i16) -> i16 {
^entry:
  cond_br %c, ^then(%a), ^else(%b) @0
^then(%x: i16):
  ret %x @0
^else(%y: i16):
  ret %y @0
}

locs {
  @0 = unknown
}
