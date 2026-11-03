func @sdiv_left(%a: i128, %b: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = sdiv %p, %b @0
  ret %r @0
}

func @sdiv_right(%a: i128, %b: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = sdiv %b, %p @0
  ret %r @0
}

func @sdiv_both(%a: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = sdiv %p, %p @0
  ret %r @0
}

func @sdiv_exact_left(%a: i128, %b: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = sdiv exact %p, %b @0
  ret %r @0
}

func @sdiv_exact_right(%a: i128, %b: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = sdiv exact %b, %p @0
  ret %r @0
}

func @sdiv_exact_both(%a: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = sdiv exact %p, %p @0
  ret %r @0
}

func @udiv_left(%a: i128, %b: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = udiv %p, %b @0
  ret %r @0
}

func @udiv_right(%a: i128, %b: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = udiv %b, %p @0
  ret %r @0
}

func @udiv_both(%a: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = udiv %p, %p @0
  ret %r @0
}

func @udiv_exact_left(%a: i128, %b: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = udiv exact %p, %b @0
  ret %r @0
}

func @udiv_exact_right(%a: i128, %b: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = udiv exact %b, %p @0
  ret %r @0
}

func @udiv_exact_both(%a: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = udiv exact %p, %p @0
  ret %r @0
}

func @srem_left(%a: i128, %b: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = srem %p, %b @0
  ret %r @0
}

func @srem_right(%a: i128, %b: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = srem %b, %p @0
  ret %r @0
}

func @srem_both(%a: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = srem %p, %p @0
  ret %r @0
}

func @urem_left(%a: i128, %b: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = urem %p, %b @0
  ret %r @0
}

func @urem_right(%a: i128, %b: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = urem %b, %p @0
  ret %r @0
}

func @urem_both(%a: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %r: i128 = urem %p, %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
