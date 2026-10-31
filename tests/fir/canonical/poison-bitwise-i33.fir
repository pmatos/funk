func @and_left(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = and %p, %b @0
  ret %r @0
}

func @and_right(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = and %b, %p @0
  ret %r @0
}

func @or_left(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = or %p, %b @0
  ret %r @0
}

func @or_right(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = or %b, %p @0
  ret %r @0
}

func @xor_left(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = xor %p, %b @0
  ret %r @0
}

func @xor_right(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = xor %b, %p @0
  ret %r @0
}

func @shl_left(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = shl %p, %b @0
  ret %r @0
}

func @shl_right(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = shl %b, %p @0
  ret %r @0
}

func @lshr_left(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = lshr %p, %b @0
  ret %r @0
}

func @lshr_right(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = lshr %b, %p @0
  ret %r @0
}

func @ashr_left(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = ashr %p, %b @0
  ret %r @0
}

func @ashr_right(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = ashr %b, %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
