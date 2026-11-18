layout memory(1, unit(16), pointer(32), little)

aggregate @wide() memory(1) size(8) align(4) field(0, ptr(1)) field(2, i16, 2) field(4, ptr) {
}

aggregate @i24s() memory(1) size(6) align(2) field(0, i24, 2) {
}

module @dev() {
  aggregate @cell() memory(1) size(2) align(2) field(0, ptr(1)) {
  }

}

func @wide_size() -> i64 {
^entry:
  %s: i64 = const 8 @0
  ret %s @0
}

locs {
  @0 = unknown
}
