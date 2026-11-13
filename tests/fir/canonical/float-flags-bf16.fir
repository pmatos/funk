func @fcmp_nnan(%a: bf16, %b: bf16) -> i1 {
^entry:
  %r: i1 = fcmp nnan uno %a, %b @0
  ret %r @0
}

func @fadd_nnan(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fadd nnan round(rne) %a, %b @0
  ret %r @0
}

func @fsub_nnan(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fsub nnan round(rne) %a, %b @0
  ret %r @0
}

func @fmul_nnan(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fmul nnan round(rne) %a, %b @0
  ret %r @0
}

func @fdiv_nnan(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fdiv nnan round(rne) %a, %b @0
  ret %r @0
}

func @frem_nnan(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = frem nnan %a, %b @0
  ret %r @0
}

func @fmod_nnan(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fmod nnan %a, %b @0
  ret %r @0
}

func @fneg_nnan(%a: bf16) -> bf16 {
^entry:
  %r: bf16 = fneg nnan %a @0
  ret %r @0
}

func @fabs_nnan(%a: bf16) -> bf16 {
^entry:
  %r: bf16 = fabs nnan %a @0
  ret %r @0
}

func @sqrt_nnan(%a: bf16) -> bf16 {
^entry:
  %r: bf16 = sqrt nnan round(rne) %a @0
  ret %r @0
}

func @fma_nnan(%a: bf16, %b: bf16, %c: bf16) -> bf16 {
^entry:
  %r: bf16 = fma nnan round(rne) %a, %b, %c @0
  ret %r @0
}

func @fcmp_ninf(%a: bf16, %b: bf16) -> i1 {
^entry:
  %r: i1 = fcmp ninf olt %a, %b @0
  ret %r @0
}

func @fadd_ninf(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fadd ninf round(rne) %a, %b @0
  ret %r @0
}

func @fsub_ninf(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fsub ninf round(rne) %a, %b @0
  ret %r @0
}

func @fmul_ninf(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fmul ninf round(rne) %a, %b @0
  ret %r @0
}

func @fdiv_ninf(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fdiv ninf round(rne) %a, %b @0
  ret %r @0
}

func @frem_ninf(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = frem ninf %a, %b @0
  ret %r @0
}

func @fmod_ninf(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fmod ninf %a, %b @0
  ret %r @0
}

func @fneg_ninf(%a: bf16) -> bf16 {
^entry:
  %r: bf16 = fneg ninf %a @0
  ret %r @0
}

func @fabs_ninf(%a: bf16) -> bf16 {
^entry:
  %r: bf16 = fabs ninf %a @0
  ret %r @0
}

func @sqrt_ninf(%a: bf16) -> bf16 {
^entry:
  %r: bf16 = sqrt ninf round(rne) %a @0
  ret %r @0
}

func @fma_ninf(%a: bf16, %b: bf16, %c: bf16) -> bf16 {
^entry:
  %r: bf16 = fma ninf round(rne) %a, %b, %c @0
  ret %r @0
}

func @fcmp_nsz(%a: bf16, %b: bf16) -> i1 {
^entry:
  %r: i1 = fcmp nsz oeq %a, %b @0
  ret %r @0
}

func @fadd_nsz(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fadd nsz round(rne) %a, %b @0
  ret %r @0
}

func @fsub_nsz(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fsub nsz round(rne) %a, %b @0
  ret %r @0
}

func @fmul_nsz(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fmul nsz round(rne) %a, %b @0
  ret %r @0
}

func @fdiv_nsz(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fdiv nsz round(rne) %a, %b @0
  ret %r @0
}

func @frem_nsz(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = frem nsz %a, %b @0
  ret %r @0
}

func @fmod_nsz(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fmod nsz %a, %b @0
  ret %r @0
}

func @fneg_nsz(%a: bf16) -> bf16 {
^entry:
  %r: bf16 = fneg nsz %a @0
  ret %r @0
}

func @fabs_nsz(%a: bf16) -> bf16 {
^entry:
  %r: bf16 = fabs nsz %a @0
  ret %r @0
}

func @sqrt_nsz(%a: bf16) -> bf16 {
^entry:
  %r: bf16 = sqrt nsz round(rne) %a @0
  ret %r @0
}

func @fma_nsz(%a: bf16, %b: bf16, %c: bf16) -> bf16 {
^entry:
  %r: bf16 = fma nsz round(rne) %a, %b, %c @0
  ret %r @0
}

locs {
  @0 = unknown
}
