func @ueq(%a: f64, %b: f64) -> i1 {
^entry:
  %r: i1 = fcmp ueq %a, %b @0
  ret %r @0
}

func @une(%a: f64, %b: f64) -> i1 {
^entry:
  %r: i1 = fcmp une %a, %b @0
  ret %r @0
}

func @ult(%a: f64, %b: f64) -> i1 {
^entry:
  %r: i1 = fcmp ult %a, %b @0
  ret %r @0
}

func @ule(%a: f64, %b: f64) -> i1 {
^entry:
  %r: i1 = fcmp ule %a, %b @0
  ret %r @0
}

func @ugt(%a: f64, %b: f64) -> i1 {
^entry:
  %r: i1 = fcmp ugt %a, %b @0
  ret %r @0
}

func @uge(%a: f64, %b: f64) -> i1 {
^entry:
  %r: i1 = fcmp uge %a, %b @0
  ret %r @0
}

func @uno(%a: f64, %b: f64) -> i1 {
^entry:
  %r: i1 = fcmp uno %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
