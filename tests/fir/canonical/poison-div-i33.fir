func @sdiv_left(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = sdiv %p, %b @0
  ret %r @0
}

func @sdiv_right(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = sdiv %b, %p @0
  ret %r @0
}

func @sdiv_both(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = sdiv %p, %p @0
  ret %r @0
}

func @sdiv_exact_left(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = sdiv exact %p, %b @0
  ret %r @0
}

func @sdiv_exact_right(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = sdiv exact %b, %p @0
  ret %r @0
}

func @sdiv_exact_both(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = sdiv exact %p, %p @0
  ret %r @0
}

func @udiv_left(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = udiv %p, %b @0
  ret %r @0
}

func @udiv_right(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = udiv %b, %p @0
  ret %r @0
}

func @udiv_both(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = udiv %p, %p @0
  ret %r @0
}

func @udiv_exact_left(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = udiv exact %p, %b @0
  ret %r @0
}

func @udiv_exact_right(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = udiv exact %b, %p @0
  ret %r @0
}

func @udiv_exact_both(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = udiv exact %p, %p @0
  ret %r @0
}

func @srem_left(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = srem %p, %b @0
  ret %r @0
}

func @srem_right(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = srem %b, %p @0
  ret %r @0
}

func @srem_both(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = srem %p, %p @0
  ret %r @0
}

func @urem_left(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = urem %p, %b @0
  ret %r @0
}

func @urem_right(%a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = urem %b, %p @0
  ret %r @0
}

func @urem_both(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = urem %p, %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
