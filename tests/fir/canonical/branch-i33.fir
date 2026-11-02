func @br(%a: i33) -> i33 {
^entry:
  br ^next(%a) @0
^next(%x: i33):
  ret %x @0
}

func @cond_br(%c: i1, %a: i33, %b: i33) -> i33 {
^entry:
  cond_br %c, ^then(%a), ^else(%b) @0
^then(%x: i33):
  ret %x @0
^else(%y: i33):
  ret %y @0
}

locs {
  @0 = unknown
}
