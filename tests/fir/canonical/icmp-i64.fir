func @eq(%a: i64, %b: i64) -> i1 {
^entry:
  %r: i1 = icmp eq %a, %b @0
  ret %r @0
}

func @ne(%a: i64, %b: i64) -> i1 {
^entry:
  %r: i1 = icmp ne %a, %b @0
  ret %r @0
}

func @slt(%a: i64, %b: i64) -> i1 {
^entry:
  %r: i1 = icmp slt %a, %b @0
  ret %r @0
}

func @sle(%a: i64, %b: i64) -> i1 {
^entry:
  %r: i1 = icmp sle %a, %b @0
  ret %r @0
}

func @sgt(%a: i64, %b: i64) -> i1 {
^entry:
  %r: i1 = icmp sgt %a, %b @0
  ret %r @0
}

func @sge(%a: i64, %b: i64) -> i1 {
^entry:
  %r: i1 = icmp sge %a, %b @0
  ret %r @0
}

func @ult(%a: i64, %b: i64) -> i1 {
^entry:
  %r: i1 = icmp ult %a, %b @0
  ret %r @0
}

func @ule(%a: i64, %b: i64) -> i1 {
^entry:
  %r: i1 = icmp ule %a, %b @0
  ret %r @0
}

func @ugt(%a: i64, %b: i64) -> i1 {
^entry:
  %r: i1 = icmp ugt %a, %b @0
  ret %r @0
}

func @uge(%a: i64, %b: i64) -> i1 {
^entry:
  %r: i1 = icmp uge %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
