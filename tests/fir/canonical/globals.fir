data @msg() size(8) align(1) constant units(104, 105, 0) {
}

data @table() size(24) align(8) export addr(@msg) addr(@msg, 3) zeros(8) {
}

data @counter() size(4) align(4) {
}

data @self() size(16) align(8) constant export addr(@self, 8) units(1, 0, 0, 0, 0, 0, 0, 0) {
}

func @msg_size() -> i64 {
^entry:
  %s: i64 = const 8 @0
  ret %s @0
}

locs {
  @0 = unknown
}
