func @br(%a: i128) -> i128 {
^entry:
  br ^next(%a) @0
^next(%x: i128):
  ret %x @0
}

func @cond_br(%c: i1, %a: i128, %b: i128) -> i128 {
^entry:
  cond_br %c, ^then(%a), ^else(%b) @0
^then(%x: i128):
  ret %x @0
^else(%y: i128):
  ret %y @0
}

locs {
  @0 = unknown
}
