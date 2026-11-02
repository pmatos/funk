func @id(%a: i7) -> i7 {
^entry:
  ret %a @0
}

func @passes(%a: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = call @id %p @0
  ret %r @0
}

func @makes(%a: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  ret %p @0
}

func @receives(%a: i7) -> i7 {
^entry:
  %r: i7 = call @makes %a @0
  %one: i7 = const 1 @0
  %s: i7 = add %r, %one @0
  ret %s @0
}

func @zero(%a: i7) -> i7 {
^entry:
  %z: i7 = const 0 @0
  ret %z @0
}

func @ignores(%a: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = call @zero %p @0
  ret %r @0
}

func @branches(%a: i7) -> i7 {
^entry:
  %z: i7 = const 0 @0
  %c: i1 = icmp eq %a, %z @0
  cond_br %c, ^yes, ^no @0
^yes:
  %one: i7 = const 1 @0
  ret %one @0
^no:
  ret %a @0
}

func @branches_on(%a: i7) -> i7 {
^entry:
  %one: i7 = const 1 @0
  %p: i7 = add nsw %a, %one @0
  %r: i7 = call @branches %p @0
  ret %r @0
}

func @div(%a: i7, %b: i7) -> i7 {
^entry:
  %q: i7 = udiv %a, %b @0
  ret %q @0
}

func @calls_div(%a: i7, %b: i7) -> i7 {
^entry:
  %q: i7 = call @div %a, %b @0
  ret %q @0
}

locs {
  @0 = unknown
}
