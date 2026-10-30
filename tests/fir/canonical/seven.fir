func @seven() -> i32 {
^entry:
  %c: i32 = const 7 @0
  ret %c @0
}

locs {
  @0 = unknown
}
