func @sdiv_left(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = sdiv %p, %b @0
  ret %r @0
}

func @sdiv_right(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = sdiv %b, %p @0
  ret %r @0
}

func @sdiv_both(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = sdiv %p, %p @0
  ret %r @0
}

func @sdiv_exact_left(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = sdiv exact %p, %b @0
  ret %r @0
}

func @sdiv_exact_right(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = sdiv exact %b, %p @0
  ret %r @0
}

func @sdiv_exact_both(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = sdiv exact %p, %p @0
  ret %r @0
}

func @udiv_left(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = udiv %p, %b @0
  ret %r @0
}

func @udiv_right(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = udiv %b, %p @0
  ret %r @0
}

func @udiv_both(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = udiv %p, %p @0
  ret %r @0
}

func @udiv_exact_left(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = udiv exact %p, %b @0
  ret %r @0
}

func @udiv_exact_right(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = udiv exact %b, %p @0
  ret %r @0
}

func @udiv_exact_both(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = udiv exact %p, %p @0
  ret %r @0
}

func @srem_left(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = srem %p, %b @0
  ret %r @0
}

func @srem_right(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = srem %b, %p @0
  ret %r @0
}

func @srem_both(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = srem %p, %p @0
  ret %r @0
}

func @urem_left(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = urem %p, %b @0
  ret %r @0
}

func @urem_right(%a: i1, %b: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = urem %b, %p @0
  ret %r @0
}

func @urem_both(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = urem %p, %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
