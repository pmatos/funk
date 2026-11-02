func @id(%a: i7) -> i7 {
^entry:
  ret %a @0
}

func @call_id(%a: i7) -> i7 {
^entry:
  %r: i7 = call @id %a @0
  ret %r @0
}

func @sub(%a: i7, %b: i7) -> i7 {
^entry:
  %d: i7 = sub %a, %b @0
  ret %d @0
}

func @call_sub(%a: i7, %b: i7) -> i7 {
^entry:
  %r: i7 = call @sub %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
