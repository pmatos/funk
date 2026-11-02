func @swap(%a: i8, %b: i16, %c: i1) -> i1, i16, i8 {
^entry:
  ret %c, %b, %a @0
}

func @call_swap(%a: i8, %b: i16, %c: i1) -> i8, i16, i1 {
^entry:
  %x: i1, %y: i16, %z: i8 = call @swap %a, %b, %c @0
  ret %z, %y, %x @0
}

func @divmod(%a: i32, %b: i32) -> i32, i32 {
^entry:
  %q: i32 = udiv %a, %b @0
  %r: i32 = urem %a, %b @0
  ret %q, %r @0
}

func @call_divmod(%a: i32, %b: i32) -> i32 {
^entry:
  %q: i32, %r: i32 = call @divmod %a, %b @0
  %m: i32 = mul %q, %b @0
  %s: i32 = add %m, %r @0
  ret %s @0
}

locs {
  @0 = unknown
}
