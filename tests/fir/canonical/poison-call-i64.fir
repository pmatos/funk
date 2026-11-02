func @id(%a: i64) -> i64 {
^entry:
  ret %a @0
}

func @passes(%a: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i64 = call @id %p @0
  ret %r @0
}

func @makes(%a: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  ret %p @0
}

func @receives(%a: i64) -> i64 {
^entry:
  %r: i64 = call @makes %a @0
  %one: i64 = const 1 @0
  %s: i64 = add %r, %one @0
  ret %s @0
}

func @zero(%a: i64) -> i64 {
^entry:
  %z: i64 = const 0 @0
  ret %z @0
}

func @ignores(%a: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i64 = call @zero %p @0
  ret %r @0
}

func @branches(%a: i64) -> i64 {
^entry:
  %z: i64 = const 0 @0
  %c: i1 = icmp eq %a, %z @0
  cond_br %c, ^yes, ^no @0
^yes:
  %one: i64 = const 1 @0
  ret %one @0
^no:
  ret %a @0
}

func @branches_on(%a: i64) -> i64 {
^entry:
  %one: i64 = const 1 @0
  %p: i64 = add nsw %a, %one @0
  %r: i64 = call @branches %p @0
  ret %r @0
}

func @div(%a: i64, %b: i64) -> i64 {
^entry:
  %q: i64 = udiv %a, %b @0
  ret %q @0
}

func @calls_div(%a: i64, %b: i64) -> i64 {
^entry:
  %q: i64 = call @div %a, %b @0
  ret %q @0
}

locs {
  @0 = unknown
}
