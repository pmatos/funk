func @and_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = and %p, %b @0
  ret %r @0
}

func @and_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = and %b, %p @0
  ret %r @0
}

func @or_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = or %p, %b @0
  ret %r @0
}

func @or_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = or %b, %p @0
  ret %r @0
}

func @xor_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = xor %p, %b @0
  ret %r @0
}

func @xor_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = xor %b, %p @0
  ret %r @0
}

func @shl_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = shl %p, %b @0
  ret %r @0
}

func @shl_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = shl %b, %p @0
  ret %r @0
}

func @lshr_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = lshr %p, %b @0
  ret %r @0
}

func @lshr_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = lshr %b, %p @0
  ret %r @0
}

func @ashr_left(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = ashr %p, %b @0
  ret %r @0
}

func @ashr_right(%a: i7, %b: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = ashr %b, %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
