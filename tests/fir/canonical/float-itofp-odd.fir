func @si_i7_f16(%a: i7) -> f16 {
^entry:
  %r: f16 = sitofp round(rne) %a @0
  ret %r @0
}

func @ui_i7_f16(%a: i7) -> f16 {
^entry:
  %r: f16 = uitofp round(rne) %a @0
  ret %r @0
}

func @si_i7_bf16(%a: i7) -> bf16 {
^entry:
  %r: bf16 = sitofp round(rne) %a @0
  ret %r @0
}

func @ui_i7_bf16(%a: i7) -> bf16 {
^entry:
  %r: bf16 = uitofp round(rne) %a @0
  ret %r @0
}

func @si_i7_f32(%a: i7) -> f32 {
^entry:
  %r: f32 = sitofp round(rne) %a @0
  ret %r @0
}

func @ui_i7_f32(%a: i7) -> f32 {
^entry:
  %r: f32 = uitofp round(rne) %a @0
  ret %r @0
}

func @si_i7_f64(%a: i7) -> f64 {
^entry:
  %r: f64 = sitofp round(rne) %a @0
  ret %r @0
}

func @ui_i7_f64(%a: i7) -> f64 {
^entry:
  %r: f64 = uitofp round(rne) %a @0
  ret %r @0
}

func @si_i7_f128(%a: i7) -> f128 {
^entry:
  %r: f128 = sitofp round(rne) %a @0
  ret %r @0
}

func @ui_i7_f128(%a: i7) -> f128 {
^entry:
  %r: f128 = uitofp round(rne) %a @0
  ret %r @0
}

func @si_i33_f16(%a: i33) -> f16 {
^entry:
  %r: f16 = sitofp round(rne) %a @0
  ret %r @0
}

func @ui_i33_f16(%a: i33) -> f16 {
^entry:
  %r: f16 = uitofp round(rne) %a @0
  ret %r @0
}

func @si_i33_bf16(%a: i33) -> bf16 {
^entry:
  %r: bf16 = sitofp round(rne) %a @0
  ret %r @0
}

func @ui_i33_bf16(%a: i33) -> bf16 {
^entry:
  %r: bf16 = uitofp round(rne) %a @0
  ret %r @0
}

func @si_i33_f32(%a: i33) -> f32 {
^entry:
  %r: f32 = sitofp round(rne) %a @0
  ret %r @0
}

func @ui_i33_f32(%a: i33) -> f32 {
^entry:
  %r: f32 = uitofp round(rne) %a @0
  ret %r @0
}

func @si_i33_f64(%a: i33) -> f64 {
^entry:
  %r: f64 = sitofp round(rne) %a @0
  ret %r @0
}

func @ui_i33_f64(%a: i33) -> f64 {
^entry:
  %r: f64 = uitofp round(rne) %a @0
  ret %r @0
}

func @si_i33_f128(%a: i33) -> f128 {
^entry:
  %r: f128 = sitofp round(rne) %a @0
  ret %r @0
}

func @ui_i33_f128(%a: i33) -> f128 {
^entry:
  %r: f128 = uitofp round(rne) %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
