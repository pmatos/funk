func @ui_i1(%a: i1) -> f16 {
^entry:
  %r: f16 = uitofp round(rne) %a @0
  ret %r @0
}

func @ui_i8(%a: i8) -> f16 {
^entry:
  %r: f16 = uitofp round(rne) %a @0
  ret %r @0
}

func @ui_i16(%a: i16) -> f16 {
^entry:
  %r: f16 = uitofp round(rne) %a @0
  ret %r @0
}

func @ui_i32(%a: i32) -> f16 {
^entry:
  %r: f16 = uitofp round(rne) %a @0
  ret %r @0
}

func @ui_i64(%a: i64) -> f16 {
^entry:
  %r: f16 = uitofp round(rne) %a @0
  ret %r @0
}

func @ui_i128(%a: i128) -> f16 {
^entry:
  %r: f16 = uitofp round(rne) %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
