func @ui_i1(%a: i1) -> bf16 {
^entry:
  %r: bf16 = uitofp round(rne) %a @0
  ret %r @0
}

func @ui_i8(%a: i8) -> bf16 {
^entry:
  %r: bf16 = uitofp round(rne) %a @0
  ret %r @0
}

func @ui_i16(%a: i16) -> bf16 {
^entry:
  %r: bf16 = uitofp round(rne) %a @0
  ret %r @0
}

func @ui_i32(%a: i32) -> bf16 {
^entry:
  %r: bf16 = uitofp round(rne) %a @0
  ret %r @0
}

func @ui_i64(%a: i64) -> bf16 {
^entry:
  %r: bf16 = uitofp round(rne) %a @0
  ret %r @0
}

func @ui_i128(%a: i128) -> bf16 {
^entry:
  %r: bf16 = uitofp round(rne) %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
