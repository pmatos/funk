func @id(%a: i33) -> i33 {
^entry:
  ret %a @0
}

func @call_id(%a: i33) -> i33 {
^entry:
  %r: i33 = call @id %a @0
  ret %r @0
}

func @sub(%a: i33, %b: i33) -> i33 {
^entry:
  %d: i33 = sub %a, %b @0
  ret %d @0
}

func @call_sub(%a: i33, %b: i33) -> i33 {
^entry:
  %r: i33 = call @sub %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
