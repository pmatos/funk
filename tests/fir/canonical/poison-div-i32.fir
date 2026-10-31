func @sdiv_left(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = sdiv %p, %b @0
  ret %r @0
}

func @sdiv_right(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = sdiv %b, %p @0
  ret %r @0
}

func @sdiv_exact_left(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = sdiv exact %p, %b @0
  ret %r @0
}

func @sdiv_exact_right(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = sdiv exact %b, %p @0
  ret %r @0
}

func @udiv_left(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = udiv %p, %b @0
  ret %r @0
}

func @udiv_right(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = udiv %b, %p @0
  ret %r @0
}

func @udiv_exact_left(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = udiv exact %p, %b @0
  ret %r @0
}

func @udiv_exact_right(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = udiv exact %b, %p @0
  ret %r @0
}

func @srem_left(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = srem %p, %b @0
  ret %r @0
}

func @srem_right(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = srem %b, %p @0
  ret %r @0
}

func @urem_left(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = urem %p, %b @0
  ret %r @0
}

func @urem_right(%a: i32, %b: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = urem %b, %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
