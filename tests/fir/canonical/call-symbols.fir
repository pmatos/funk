func @"1"(%a: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %s: i32 = add %a, %one @0
  ret %s @0
}

func @caller(%a: i32) -> i32 {
^entry:
  %r: i32 = call @"1" %a @0
  ret %r @0
}

locs {
  @0 = unknown
}
