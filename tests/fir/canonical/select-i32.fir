func @select(%c: i1, %a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = select %c, %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
