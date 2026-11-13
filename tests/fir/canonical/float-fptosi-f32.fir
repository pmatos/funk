func @s_i1(%a: f32) -> i1 {
^entry:
  %r: i1 = fptosi %a @0
  ret %r @0
}

func @s_i8(%a: f32) -> i8 {
^entry:
  %r: i8 = fptosi %a @0
  ret %r @0
}

func @s_i16(%a: f32) -> i16 {
^entry:
  %r: i16 = fptosi %a @0
  ret %r @0
}

func @s_i32(%a: f32) -> i32 {
^entry:
  %r: i32 = fptosi %a @0
  ret %r @0
}

func @s_i64(%a: f32) -> i64 {
^entry:
  %r: i64 = fptosi %a @0
  ret %r @0
}

func @s_i128(%a: f32) -> i128 {
^entry:
  %r: i128 = fptosi %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
