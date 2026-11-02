func @id(%a: i1) -> i1 {
^entry:
  ret %a @0
}

func @call_id(%a: i1) -> i1 {
^entry:
  %r: i1 = call @id %a @0
  ret %r @0
}

func @sub(%a: i1, %b: i1) -> i1 {
^entry:
  %d: i1 = sub %a, %b @0
  ret %d @0
}

func @call_sub(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = call @sub %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
