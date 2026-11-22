layout memory(1, unit(16), pointer(32), little)

global @wide() memory(1) size(4) align(2) const units(65535, 1) addr(@wide, 1) {
}

global @narrow() size(8) align(8) units(42) {
}

module @dev() {
  global @cell() memory(1) size(2) align(2) units(300) {
  }

  func @read_cell() -> i16 {
  ^entry:
    %c: ptr(1) = globaladdr @cell @0
    %v: i16 = load nonatomic %c @0
    ret %v @0
  }

  func @cell_address() -> ptr(1) {
  ^entry:
    %c: ptr(1) = globaladdr @cell @0
    ret %c @0
  }

}

func @wide_unit(%i: i32) -> i16 {
^entry:
  %w: ptr(1) = globaladdr @wide @0
  %p: ptr(1) = ptradd %w, %i @0
  %v: i16 = load nonatomic %p @0
  ret %v @0
}

func @wide_self() -> i16 {
^entry:
  %w: ptr(1) = globaladdr @wide @0
  %k: i32 = const 2 @0
  %e: ptr(1) = ptradd %w, %k @0
  %p: ptr(1) = load nonatomic %e @0
  %v: i16 = load nonatomic %p @0
  ret %v @0
}

func @narrow_value() -> i64 {
^entry:
  %n: ptr = globaladdr @narrow @0
  %v: i64 = load nonatomic %n @0
  ret %v @0
}

func @addresses() -> ptr(1), ptr {
^entry:
  %w: ptr(1) = globaladdr @wide @0
  %n: ptr = globaladdr @narrow @0
  ret %w, %n @0
}

locs {
  @0 = unknown
}
