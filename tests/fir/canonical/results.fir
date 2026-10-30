func @none() {
^entry:
  ret @0
}

func @one(%x: i8) -> i8 {
^entry:
  ret %x @0
}

func @several(%x: i8, %y: i16) -> i16, i8, i8 {
^entry:
  %one: i8 = const 1 @0
  %z: i8 = add %x, %one @0
  ret %y, %z, %x @0
}

func @unused(%x: i64) {
^entry:
  %y: i64 = add %x, %x @0
  ret @0
}

locs {
  @0 = unknown
}
