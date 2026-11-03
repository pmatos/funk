func @id(%a: i128) -> i128 {
^entry:
  ret %a @0
}

func @call_id(%a: i128) -> i128 {
^entry:
  %r: i128 = call @id %a @0
  ret %r @0
}

func @sub(%a: i128, %b: i128) -> i128 {
^entry:
  %d: i128 = sub %a, %b @0
  ret %d @0
}

func @call_sub(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = call @sub %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
