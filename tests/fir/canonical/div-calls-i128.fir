func @divmod(%a: i128, %b: i128) -> i128, i128 {
^entry:
  %q: i128 = sdiv %a, %b @0
  %r: i128 = srem %a, %b @0
  ret %q, %r @0
}

func @udivmod(%a: i128, %b: i128) -> i64, i128, i128 {
^entry:
  %q: i128 = udiv %a, %b @0
  %r: i128 = urem %a, %b @0
  %t: i64 = trunc %q @0
  ret %t, %q, %r @0
}

func @recompose(%a: i128, %b: i128) -> i128 {
^entry:
  %q: i128, %r: i128 = call @divmod %a, %b @0
  %m: i128 = mul %q, %b @0
  %s: i128 = add %m, %r @0
  ret %s @0
}

func @nested(%a: i128, %b: i128, %c: i128) -> i128, i64 {
^entry:
  %q: i128 = sdiv %a, %b @0
  %t: i64, %x: i128, %y: i128 = call @udivmod %q, %c @0
  %z: i128 = srem %y, %c @0
  ret %z, %t @0
}

func @exact_arg(%a: i128, %b: i128) -> i128, i128 {
^entry:
  %q: i128 = sdiv exact %a, %b @0
  %x: i128, %y: i128 = call @divmod %q, %b @0
  ret %x, %y @0
}

locs {
  @0 = unknown
}
