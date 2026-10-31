func @and_left(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = and %p, %b @0
  ret %r @0
}

func @and_right(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = and %b, %p @0
  ret %r @0
}

func @or_left(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = or %p, %b @0
  ret %r @0
}

func @or_right(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = or %b, %p @0
  ret %r @0
}

func @xor_left(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = xor %p, %b @0
  ret %r @0
}

func @xor_right(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = xor %b, %p @0
  ret %r @0
}

func @shl_left(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = shl %p, %b @0
  ret %r @0
}

func @shl_right(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = shl %b, %p @0
  ret %r @0
}

func @lshr_left(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = lshr %p, %b @0
  ret %r @0
}

func @lshr_right(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = lshr %b, %p @0
  ret %r @0
}

func @ashr_left(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = ashr %p, %b @0
  ret %r @0
}

func @ashr_right(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = ashr %b, %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
