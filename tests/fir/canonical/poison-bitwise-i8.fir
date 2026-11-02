func @and_left(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = and %p, %b @0
  ret %r @0
}

func @and_right(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = and %b, %p @0
  ret %r @0
}

func @or_left(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = or %p, %b @0
  ret %r @0
}

func @or_right(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = or %b, %p @0
  ret %r @0
}

func @xor_left(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = xor %p, %b @0
  ret %r @0
}

func @xor_right(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = xor %b, %p @0
  ret %r @0
}

func @shl_left(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = shl %p, %b @0
  ret %r @0
}

func @shl_right(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = shl %b, %p @0
  ret %r @0
}

func @lshr_left(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = lshr %p, %b @0
  ret %r @0
}

func @lshr_right(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = lshr %b, %p @0
  ret %r @0
}

func @ashr_left(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = ashr %p, %b @0
  ret %r @0
}

func @ashr_right(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = ashr %b, %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
