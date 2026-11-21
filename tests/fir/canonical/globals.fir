global @msg() size(8) align(1) const units(104, 105, 0) {
}

global @table() size(24) align(8) export addr(@msg) addr(@msg, 3) zeros(8) {
}

global @counter() size(4) align(4) {
}

global @self() size(16) align(8) const export addr(@self, 8) units(1, 0, 0, 0, 0, 0, 0, 0) {
}

func @msg_size() -> i64 {
^entry:
  %s: i64 = const 8 @0
  ret %s @0
}

func @after_globals() -> ptr {
^entry:
  %p: ptr = alloca stack i32 @0
  ret %p @0
}

locs {
  @0 = unknown
}
