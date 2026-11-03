func @slt(%a: i128, %b: i128) -> i1 {
^entry:
  %r: i1 = icmp slt %a, %b @0
  ret %r @0
}

func @sle(%a: i128, %b: i128) -> i1 {
^entry:
  %r: i1 = icmp sle %a, %b @0
  ret %r @0
}

func @sgt(%a: i128, %b: i128) -> i1 {
^entry:
  %r: i1 = icmp sgt %a, %b @0
  ret %r @0
}

func @sge(%a: i128, %b: i128) -> i1 {
^entry:
  %r: i1 = icmp sge %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
