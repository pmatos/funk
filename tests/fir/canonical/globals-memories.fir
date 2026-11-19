layout memory(1, unit(16), pointer(32), little)

data @wide() memory(1) size(8) align(2) constant units(65535, 1) addr(@wide, 1) addr(@narrow) {
}

data @narrow() size(8) align(8) {
}

module @dev() {
  data @cell() memory(1) size(2) align(2) export addr(@cell) {
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
