func @eq(%a: i33, %b: i33) -> i1 {
^entry:
  %r: i1 = icmp eq %a, %b @0
  ret %r @0
}

func @ne(%a: i33, %b: i33) -> i1 {
^entry:
  %r: i1 = icmp ne %a, %b @0
  ret %r @0
}

func @slt(%a: i33, %b: i33) -> i1 {
^entry:
  %r: i1 = icmp slt %a, %b @0
  ret %r @0
}

func @sle(%a: i33, %b: i33) -> i1 {
^entry:
  %r: i1 = icmp sle %a, %b @0
  ret %r @0
}

func @sgt(%a: i33, %b: i33) -> i1 {
^entry:
  %r: i1 = icmp sgt %a, %b @0
  ret %r @0
}

func @sge(%a: i33, %b: i33) -> i1 {
^entry:
  %r: i1 = icmp sge %a, %b @0
  ret %r @0
}

func @ult(%a: i33, %b: i33) -> i1 {
^entry:
  %r: i1 = icmp ult %a, %b @0
  ret %r @0
}

func @ule(%a: i33, %b: i33) -> i1 {
^entry:
  %r: i1 = icmp ule %a, %b @0
  ret %r @0
}

func @ugt(%a: i33, %b: i33) -> i1 {
^entry:
  %r: i1 = icmp ugt %a, %b @0
  ret %r @0
}

func @uge(%a: i33, %b: i33) -> i1 {
^entry:
  %r: i1 = icmp uge %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
