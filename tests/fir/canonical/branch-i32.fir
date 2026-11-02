func @br(%a: i32) -> i32 {
^entry:
  br ^next(%a) @0
^next(%x: i32):
  ret %x @0
}

func @cond_br(%c: i1, %a: i32, %b: i32) -> i32 {
^entry:
  cond_br %c, ^then(%a), ^else(%b) @0
^then(%x: i32):
  ret %x @0
^else(%y: i32):
  ret %y @0
}

locs {
  @0 = unknown
}
