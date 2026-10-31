func @select(%c: i1, %a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = select %c, %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
