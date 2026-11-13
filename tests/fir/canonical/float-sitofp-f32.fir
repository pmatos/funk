func @si_i1(%a: i1) -> f32 {
^entry:
  %r: f32 = sitofp round(rne) %a @0
  ret %r @0
}

func @si_i8(%a: i8) -> f32 {
^entry:
  %r: f32 = sitofp round(rne) %a @0
  ret %r @0
}

func @si_i16(%a: i16) -> f32 {
^entry:
  %r: f32 = sitofp round(rne) %a @0
  ret %r @0
}

func @si_i32(%a: i32) -> f32 {
^entry:
  %r: f32 = sitofp round(rne) %a @0
  ret %r @0
}

func @si_i64(%a: i64) -> f32 {
^entry:
  %r: f32 = sitofp round(rne) %a @0
  ret %r @0
}

func @si_i128(%a: i128) -> f32 {
^entry:
  %r: f32 = sitofp round(rne) %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
