func @select(%c: i1, %a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = select %c, %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
