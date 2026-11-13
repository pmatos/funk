func @s_f16_i7(%a: f16) -> i7 {
^entry:
  %r: i7 = fptosi %a @0
  ret %r @0
}

func @s_f16_i33(%a: f16) -> i33 {
^entry:
  %r: i33 = fptosi %a @0
  ret %r @0
}

func @s_bf16_i7(%a: bf16) -> i7 {
^entry:
  %r: i7 = fptosi %a @0
  ret %r @0
}

func @s_bf16_i33(%a: bf16) -> i33 {
^entry:
  %r: i33 = fptosi %a @0
  ret %r @0
}

func @s_f32_i7(%a: f32) -> i7 {
^entry:
  %r: i7 = fptosi %a @0
  ret %r @0
}

func @s_f32_i33(%a: f32) -> i33 {
^entry:
  %r: i33 = fptosi %a @0
  ret %r @0
}

func @s_f64_i7(%a: f64) -> i7 {
^entry:
  %r: i7 = fptosi %a @0
  ret %r @0
}

func @s_f64_i33(%a: f64) -> i33 {
^entry:
  %r: i33 = fptosi %a @0
  ret %r @0
}

func @s_f128_i7(%a: f128) -> i7 {
^entry:
  %r: i7 = fptosi %a @0
  ret %r @0
}

func @s_f128_i33(%a: f128) -> i33 {
^entry:
  %r: i33 = fptosi %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
