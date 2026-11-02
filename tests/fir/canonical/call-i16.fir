func @id(%a: i16) -> i16 {
^entry:
  ret %a @0
}

func @call_id(%a: i16) -> i16 {
^entry:
  %r: i16 = call @id %a @0
  ret %r @0
}

func @sub(%a: i16, %b: i16) -> i16 {
^entry:
  %d: i16 = sub %a, %b @0
  ret %d @0
}

func @call_sub(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = call @sub %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
