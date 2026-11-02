func @id(%a: i32) -> i32 {
^entry:
  ret %a @0
}

func @passes(%a: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = call @id %p @0
  ret %r @0
}

func @makes(%a: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  ret %p @0
}

func @receives(%a: i32) -> i32 {
^entry:
  %r: i32 = call @makes %a @0
  %one: i32 = const 1 @0
  %s: i32 = add %r, %one @0
  ret %s @0
}

func @zero(%a: i32) -> i32 {
^entry:
  %z: i32 = const 0 @0
  ret %z @0
}

func @ignores(%a: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = call @zero %p @0
  ret %r @0
}

func @branches(%a: i32) -> i32 {
^entry:
  %z: i32 = const 0 @0
  %c: i1 = icmp eq %a, %z @0
  cond_br %c, ^yes, ^no @0
^yes:
  %one: i32 = const 1 @0
  ret %one @0
^no:
  ret %a @0
}

func @branches_on(%a: i32) -> i32 {
^entry:
  %one: i32 = const 1 @0
  %p: i32 = add nsw %a, %one @0
  %r: i32 = call @branches %p @0
  ret %r @0
}

func @div(%a: i32, %b: i32) -> i32 {
^entry:
  %q: i32 = udiv %a, %b @0
  ret %q @0
}

func @calls_div(%a: i32, %b: i32) -> i32 {
^entry:
  %q: i32 = call @div %a, %b @0
  ret %q @0
}

locs {
  @0 = unknown
}
