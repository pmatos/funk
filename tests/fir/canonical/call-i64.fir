func @id(%a: i64) -> i64 {
^entry:
  ret %a @0
}

func @call_id(%a: i64) -> i64 {
^entry:
  %r: i64 = call @id %a @0
  ret %r @0
}

func @sub(%a: i64, %b: i64) -> i64 {
^entry:
  %d: i64 = sub %a, %b @0
  ret %d @0
}

func @call_sub(%a: i64, %b: i64) -> i64 {
^entry:
  %r: i64 = call @sub %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
