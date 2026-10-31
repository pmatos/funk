func @and_left(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = and %p, %b @0
  ret %r @0
}

func @and_right(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = and %b, %p @0
  ret %r @0
}

func @or_left(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = or %p, %b @0
  ret %r @0
}

func @or_right(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = or %b, %p @0
  ret %r @0
}

func @xor_left(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = xor %p, %b @0
  ret %r @0
}

func @xor_right(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = xor %b, %p @0
  ret %r @0
}

func @shl_left(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = shl %p, %b @0
  ret %r @0
}

func @shl_right(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = shl %b, %p @0
  ret %r @0
}

func @lshr_left(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = lshr %p, %b @0
  ret %r @0
}

func @lshr_right(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = lshr %b, %p @0
  ret %r @0
}

func @ashr_left(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = ashr %p, %b @0
  ret %r @0
}

func @ashr_right(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = ashr %b, %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
