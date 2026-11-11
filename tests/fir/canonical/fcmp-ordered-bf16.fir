func @oeq(%a: bf16, %b: bf16) -> i1 {
^entry:
  %r: i1 = fcmp oeq %a, %b @0
  ret %r @0
}

func @one(%a: bf16, %b: bf16) -> i1 {
^entry:
  %r: i1 = fcmp one %a, %b @0
  ret %r @0
}

func @olt(%a: bf16, %b: bf16) -> i1 {
^entry:
  %r: i1 = fcmp olt %a, %b @0
  ret %r @0
}

func @ole(%a: bf16, %b: bf16) -> i1 {
^entry:
  %r: i1 = fcmp ole %a, %b @0
  ret %r @0
}

func @ogt(%a: bf16, %b: bf16) -> i1 {
^entry:
  %r: i1 = fcmp ogt %a, %b @0
  ret %r @0
}

func @oge(%a: bf16, %b: bf16) -> i1 {
^entry:
  %r: i1 = fcmp oge %a, %b @0
  ret %r @0
}

func @ord(%a: bf16, %b: bf16) -> i1 {
^entry:
  %r: i1 = fcmp ord %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
