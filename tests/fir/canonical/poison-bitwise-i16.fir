func @and_left(%a: i16, %b: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i16 = and %p, %b @0
  ret %r @0
}

func @and_right(%a: i16, %b: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i16 = and %b, %p @0
  ret %r @0
}

func @or_left(%a: i16, %b: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i16 = or %p, %b @0
  ret %r @0
}

func @or_right(%a: i16, %b: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i16 = or %b, %p @0
  ret %r @0
}

func @xor_left(%a: i16, %b: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i16 = xor %p, %b @0
  ret %r @0
}

func @xor_right(%a: i16, %b: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i16 = xor %b, %p @0
  ret %r @0
}

func @shl_left(%a: i16, %b: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i16 = shl %p, %b @0
  ret %r @0
}

func @shl_right(%a: i16, %b: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i16 = shl %b, %p @0
  ret %r @0
}

func @lshr_left(%a: i16, %b: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i16 = lshr %p, %b @0
  ret %r @0
}

func @lshr_right(%a: i16, %b: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i16 = lshr %b, %p @0
  ret %r @0
}

func @ashr_left(%a: i16, %b: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i16 = ashr %p, %b @0
  ret %r @0
}

func @ashr_right(%a: i16, %b: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i16 = ashr %b, %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
