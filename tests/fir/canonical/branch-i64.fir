func @br(%a: i64) -> i64 {
^entry:
  br ^next(%a) @0
^next(%x: i64):
  ret %x @0
}

func @cond_br(%c: i1, %a: i64, %b: i64) -> i64 {
^entry:
  cond_br %c, ^then(%a), ^else(%b) @0
^then(%x: i64):
  ret %x @0
^else(%y: i64):
  ret %y @0
}

locs {
  @0 = unknown
}
