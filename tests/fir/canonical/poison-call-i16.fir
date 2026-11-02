func @id(%a: i16) -> i16 {
^entry:
  ret %a @0
}

func @passes(%a: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i16 = call @id %p @0
  ret %r @0
}

func @makes(%a: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  ret %p @0
}

func @receives(%a: i16) -> i16 {
^entry:
  %r: i16 = call @makes %a @0
  %one: i16 = const 1 @0
  %s: i16 = add %r, %one @0
  ret %s @0
}

func @zero(%a: i16) -> i16 {
^entry:
  %z: i16 = const 0 @0
  ret %z @0
}

func @ignores(%a: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i16 = call @zero %p @0
  ret %r @0
}

func @branches(%a: i16) -> i16 {
^entry:
  %z: i16 = const 0 @0
  %c: i1 = icmp eq %a, %z @0
  cond_br %c, ^yes, ^no @0
^yes:
  %one: i16 = const 1 @0
  ret %one @0
^no:
  ret %a @0
}

func @branches_on(%a: i16) -> i16 {
^entry:
  %one: i16 = const 1 @0
  %p: i16 = add nsw %a, %one @0
  %r: i16 = call @branches %p @0
  ret %r @0
}

func @div(%a: i16, %b: i16) -> i16 {
^entry:
  %q: i16 = udiv %a, %b @0
  ret %q @0
}

func @calls_div(%a: i16, %b: i16) -> i16 {
^entry:
  %q: i16 = call @div %a, %b @0
  ret %q @0
}

locs {
  @0 = unknown
}
