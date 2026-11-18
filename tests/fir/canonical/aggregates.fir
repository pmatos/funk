aggregate @pair() memory(0) size(16) align(8) field(0, i64) field(8, ptr) {
}

aggregate @i24s() memory(0) size(16) align(4) field(0, i24, 4) {
}

aggregate @flex() memory(0) size(4) align(4) field(0, i32) field(4, i8, 0) {
}

aggregate @empty() memory(0) size(0) align(1) {
}

func @pair_size() -> i64 {
^entry:
  %s: i64 = const 16 @0
  ret %s @0
}

locs {
  @0 = unknown
}
