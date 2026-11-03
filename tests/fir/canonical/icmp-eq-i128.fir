func @eq(%a: i128, %b: i128) -> i1 {
^entry:
  %r: i1 = icmp eq %a, %b @0
  ret %r @0
}

func @ne(%a: i128, %b: i128) -> i1 {
^entry:
  %r: i1 = icmp ne %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
