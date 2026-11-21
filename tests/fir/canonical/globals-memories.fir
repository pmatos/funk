layout memory(1, unit(16), pointer(32), little)

global @wide() memory(1) size(8) align(2) const units(65535, 1) addr(@wide, 1) addr(@narrow) {
}

global @narrow() size(8) align(8) {
}

module @dev() {
  global @cell() memory(1) size(2) align(2) export addr(@cell) {
  }

  func @first() -> ptr {
  ^entry:
    %p: ptr = alloca stack i32 @0
    ret %p @0
  }

}

func @wide_size() -> i64 {
^entry:
  %s: i64 = const 8 @0
  ret %s @0
}

func @after_narrow() -> ptr {
^entry:
  %p: ptr = alloca stack i32 @0
  ret %p @0
}

locs {
  @0 = unknown
}
