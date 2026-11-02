func @forever(%a: i8) -> i8 {
^entry:
  %r: i8 = call @forever %a @0
  ret %r @0
}

func @ping(%a: i32) {
^entry:
  call @pong %a @0
  ret @0
}

func @pong(%a: i32) {
^entry:
  call @ping %a @0
  ret @0
}

locs {
  @0 = unknown
}
