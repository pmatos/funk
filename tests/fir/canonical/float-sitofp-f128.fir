func @si_i1(%a: i1) -> f128 {
^entry:
  %r: f128 = sitofp round(rne) %a @0
  ret %r @0
}

func @si_i8(%a: i8) -> f128 {
^entry:
  %r: f128 = sitofp round(rne) %a @0
  ret %r @0
}

func @si_i16(%a: i16) -> f128 {
^entry:
  %r: f128 = sitofp round(rne) %a @0
  ret %r @0
}

func @si_i32(%a: i32) -> f128 {
^entry:
  %r: f128 = sitofp round(rne) %a @0
  ret %r @0
}

func @si_i64(%a: i64) -> f128 {
^entry:
  %r: f128 = sitofp round(rne) %a @0
  ret %r @0
}

func @si_i128(%a: i128) -> f128 {
^entry:
  %r: f128 = sitofp round(rne) %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
