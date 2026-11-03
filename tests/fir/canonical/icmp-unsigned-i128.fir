func @ult(%a: i128, %b: i128) -> i1 {
^entry:
  %r: i1 = icmp ult %a, %b @0
  ret %r @0
}

func @ule(%a: i128, %b: i128) -> i1 {
^entry:
  %r: i1 = icmp ule %a, %b @0
  ret %r @0
}

func @ugt(%a: i128, %b: i128) -> i1 {
^entry:
  %r: i1 = icmp ugt %a, %b @0
  ret %r @0
}

func @uge(%a: i128, %b: i128) -> i1 {
^entry:
  %r: i1 = icmp uge %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
