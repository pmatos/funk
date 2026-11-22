extern @printf(%fmt: ptr, ...) -> i32 {
}

extern @abs(%n: i32) -> i32 {
}

extern @putchar(%c: i8 sext) -> i8 zext {
}

extern @abort() {
}

extern @va(...) {
}

func @twice(%a: i8 sext) -> i8 sext {
^entry:
  %s: i8 = add %a, %a @0
  ret %s @0
}

module @dev() {
  extern @g(%x: i16 zext, %y: i1 zext, ...) -> i32, i1 sext {
  }

}

locs {
  @0 = unknown
}
