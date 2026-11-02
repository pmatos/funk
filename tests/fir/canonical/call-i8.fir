func @id(%a: i8) -> i8 {
^entry:
  ret %a @0
}

func @call_id(%a: i8) -> i8 {
^entry:
  %r: i8 = call @id %a @0
  ret %r @0
}

func @sub(%a: i8, %b: i8) -> i8 {
^entry:
  %d: i8 = sub %a, %b @0
  ret %d @0
}

func @call_sub(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = call @sub %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
