func @oeq(%a: f16, %b: f16) -> i1 {
^entry:
  %r: i1 = fcmp oeq %a, %b @0
  ret %r @0
}

func @one(%a: f16, %b: f16) -> i1 {
^entry:
  %r: i1 = fcmp one %a, %b @0
  ret %r @0
}

func @olt(%a: f16, %b: f16) -> i1 {
^entry:
  %r: i1 = fcmp olt %a, %b @0
  ret %r @0
}

func @ole(%a: f16, %b: f16) -> i1 {
^entry:
  %r: i1 = fcmp ole %a, %b @0
  ret %r @0
}

func @ogt(%a: f16, %b: f16) -> i1 {
^entry:
  %r: i1 = fcmp ogt %a, %b @0
  ret %r @0
}

func @oge(%a: f16, %b: f16) -> i1 {
^entry:
  %r: i1 = fcmp oge %a, %b @0
  ret %r @0
}

func @ord(%a: f16, %b: f16) -> i1 {
^entry:
  %r: i1 = fcmp ord %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
