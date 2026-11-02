func @id(%a: i32) -> i32 {
^entry:
  ret %a @0
}

func @call_id(%a: i32) -> i32 {
^entry:
  %r: i32 = call @id %a @0
  ret %r @0
}

func @sub(%a: i32, %b: i32) -> i32 {
^entry:
  %d: i32 = sub %a, %b @0
  ret %d @0
}

func @call_sub(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = call @sub %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
