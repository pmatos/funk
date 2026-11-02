func @select(%c: i1, %a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = select %c, %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
