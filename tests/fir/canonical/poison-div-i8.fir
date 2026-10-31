func @sdiv_left(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = sdiv %p, %b @0
  ret %r @0
}

func @sdiv_right(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = sdiv %b, %p @0
  ret %r @0
}

func @sdiv_exact_left(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = sdiv exact %p, %b @0
  ret %r @0
}

func @sdiv_exact_right(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = sdiv exact %b, %p @0
  ret %r @0
}

func @udiv_left(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = udiv %p, %b @0
  ret %r @0
}

func @udiv_right(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = udiv %b, %p @0
  ret %r @0
}

func @udiv_exact_left(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = udiv exact %p, %b @0
  ret %r @0
}

func @udiv_exact_right(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = udiv exact %b, %p @0
  ret %r @0
}

func @srem_left(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = srem %p, %b @0
  ret %r @0
}

func @srem_right(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = srem %b, %p @0
  ret %r @0
}

func @urem_left(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = urem %p, %b @0
  ret %r @0
}

func @urem_right(%a: i8, %b: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = urem %b, %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
