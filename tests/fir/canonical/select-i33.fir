func @select(%c: i1, %a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = select %c, %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
