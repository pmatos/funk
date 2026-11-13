func @fcmp_nnan(%a: f16, %b: f16) -> i1 {
^entry:
  %r: i1 = fcmp nnan uno %a, %b @0
  ret %r @0
}

func @fadd_nnan(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fadd nnan round(rne) %a, %b @0
  ret %r @0
}

func @fsub_nnan(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fsub nnan round(rne) %a, %b @0
  ret %r @0
}

func @fmul_nnan(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fmul nnan round(rne) %a, %b @0
  ret %r @0
}

func @fdiv_nnan(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fdiv nnan round(rne) %a, %b @0
  ret %r @0
}

func @frem_nnan(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = frem nnan %a, %b @0
  ret %r @0
}

func @fmod_nnan(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fmod nnan %a, %b @0
  ret %r @0
}

func @fneg_nnan(%a: f16) -> f16 {
^entry:
  %r: f16 = fneg nnan %a @0
  ret %r @0
}

func @fabs_nnan(%a: f16) -> f16 {
^entry:
  %r: f16 = fabs nnan %a @0
  ret %r @0
}

func @sqrt_nnan(%a: f16) -> f16 {
^entry:
  %r: f16 = sqrt nnan round(rne) %a @0
  ret %r @0
}

func @fma_nnan(%a: f16, %b: f16, %c: f16) -> f16 {
^entry:
  %r: f16 = fma nnan round(rne) %a, %b, %c @0
  ret %r @0
}

func @fcmp_ninf(%a: f16, %b: f16) -> i1 {
^entry:
  %r: i1 = fcmp ninf olt %a, %b @0
  ret %r @0
}

func @fadd_ninf(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fadd ninf round(rne) %a, %b @0
  ret %r @0
}

func @fsub_ninf(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fsub ninf round(rne) %a, %b @0
  ret %r @0
}

func @fmul_ninf(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fmul ninf round(rne) %a, %b @0
  ret %r @0
}

func @fdiv_ninf(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fdiv ninf round(rne) %a, %b @0
  ret %r @0
}

func @frem_ninf(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = frem ninf %a, %b @0
  ret %r @0
}

func @fmod_ninf(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fmod ninf %a, %b @0
  ret %r @0
}

func @fneg_ninf(%a: f16) -> f16 {
^entry:
  %r: f16 = fneg ninf %a @0
  ret %r @0
}

func @fabs_ninf(%a: f16) -> f16 {
^entry:
  %r: f16 = fabs ninf %a @0
  ret %r @0
}

func @sqrt_ninf(%a: f16) -> f16 {
^entry:
  %r: f16 = sqrt ninf round(rne) %a @0
  ret %r @0
}

func @fma_ninf(%a: f16, %b: f16, %c: f16) -> f16 {
^entry:
  %r: f16 = fma ninf round(rne) %a, %b, %c @0
  ret %r @0
}

func @fcmp_nsz(%a: f16, %b: f16) -> i1 {
^entry:
  %r: i1 = fcmp nsz oeq %a, %b @0
  ret %r @0
}

func @fadd_nsz(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fadd nsz round(rne) %a, %b @0
  ret %r @0
}

func @fsub_nsz(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fsub nsz round(rne) %a, %b @0
  ret %r @0
}

func @fmul_nsz(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fmul nsz round(rne) %a, %b @0
  ret %r @0
}

func @fdiv_nsz(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fdiv nsz round(rne) %a, %b @0
  ret %r @0
}

func @frem_nsz(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = frem nsz %a, %b @0
  ret %r @0
}

func @fmod_nsz(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fmod nsz %a, %b @0
  ret %r @0
}

func @fneg_nsz(%a: f16) -> f16 {
^entry:
  %r: f16 = fneg nsz %a @0
  ret %r @0
}

func @fabs_nsz(%a: f16) -> f16 {
^entry:
  %r: f16 = fabs nsz %a @0
  ret %r @0
}

func @sqrt_nsz(%a: f16) -> f16 {
^entry:
  %r: f16 = sqrt nsz round(rne) %a @0
  ret %r @0
}

func @fma_nsz(%a: f16, %b: f16, %c: f16) -> f16 {
^entry:
  %r: f16 = fma nsz round(rne) %a, %b, %c @0
  ret %r @0
}

locs {
  @0 = unknown
}
