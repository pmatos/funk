func @select(%c: i1, %a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = select %c, %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
