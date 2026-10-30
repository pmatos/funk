func @names(%0: i8, %acc.1: i8, %_: i8) -> i8 {
^0:
  %1: i8 = add %0, %acc.1 @0
  %x.y.z: i8 = add %1, %_ @0
  %9.9: i8 = const 99 @0
  %A_: i8 = add %x.y.z, %9.9 @0
  ret %A_ @0
}

locs {
  @0 = unknown
}
