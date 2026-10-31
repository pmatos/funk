func @and_left(%a: i64, %b: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i64 = and %p, %b @0
  ret %r @0
}

func @and_right(%a: i64, %b: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i64 = and %b, %p @0
  ret %r @0
}

func @or_left(%a: i64, %b: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i64 = or %p, %b @0
  ret %r @0
}

func @or_right(%a: i64, %b: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i64 = or %b, %p @0
  ret %r @0
}

func @xor_left(%a: i64, %b: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i64 = xor %p, %b @0
  ret %r @0
}

func @xor_right(%a: i64, %b: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i64 = xor %b, %p @0
  ret %r @0
}

func @shl_left(%a: i64, %b: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i64 = shl %p, %b @0
  ret %r @0
}

func @shl_right(%a: i64, %b: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i64 = shl %b, %p @0
  ret %r @0
}

func @lshr_left(%a: i64, %b: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i64 = lshr %p, %b @0
  ret %r @0
}

func @lshr_right(%a: i64, %b: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i64 = lshr %b, %p @0
  ret %r @0
}

func @ashr_left(%a: i64, %b: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i64 = ashr %p, %b @0
  ret %r @0
}

func @ashr_right(%a: i64, %b: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i64 = ashr %b, %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
