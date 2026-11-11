func @oeq(%a: f32, %b: f32) -> i1 {
^entry:
  %r: i1 = fcmp oeq %a, %b @0
  ret %r @0
}

func @one(%a: f32, %b: f32) -> i1 {
^entry:
  %r: i1 = fcmp one %a, %b @0
  ret %r @0
}

func @olt(%a: f32, %b: f32) -> i1 {
^entry:
  %r: i1 = fcmp olt %a, %b @0
  ret %r @0
}

func @ole(%a: f32, %b: f32) -> i1 {
^entry:
  %r: i1 = fcmp ole %a, %b @0
  ret %r @0
}

func @ogt(%a: f32, %b: f32) -> i1 {
^entry:
  %r: i1 = fcmp ogt %a, %b @0
  ret %r @0
}

func @oge(%a: f32, %b: f32) -> i1 {
^entry:
  %r: i1 = fcmp oge %a, %b @0
  ret %r @0
}

func @ord(%a: f32, %b: f32) -> i1 {
^entry:
  %r: i1 = fcmp ord %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
