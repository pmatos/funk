func @oeq(%a: f128, %b: f128) -> i1 {
^entry:
  %r: i1 = fcmp oeq %a, %b @0
  ret %r @0
}

func @one(%a: f128, %b: f128) -> i1 {
^entry:
  %r: i1 = fcmp one %a, %b @0
  ret %r @0
}

func @olt(%a: f128, %b: f128) -> i1 {
^entry:
  %r: i1 = fcmp olt %a, %b @0
  ret %r @0
}

func @ole(%a: f128, %b: f128) -> i1 {
^entry:
  %r: i1 = fcmp ole %a, %b @0
  ret %r @0
}

func @ogt(%a: f128, %b: f128) -> i1 {
^entry:
  %r: i1 = fcmp ogt %a, %b @0
  ret %r @0
}

func @oge(%a: f128, %b: f128) -> i1 {
^entry:
  %r: i1 = fcmp oge %a, %b @0
  ret %r @0
}

func @ord(%a: f128, %b: f128) -> i1 {
^entry:
  %r: i1 = fcmp ord %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
