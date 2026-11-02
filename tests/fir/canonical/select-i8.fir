func @select(%c: i1, %a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = select %c, %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
