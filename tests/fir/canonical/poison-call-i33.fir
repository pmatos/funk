func @id(%a: i33) -> i33 {
^entry:
  ret %a @0
}

func @passes(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = call @id %p @0
  ret %r @0
}

func @makes(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  ret %p @0
}

func @receives(%a: i33) -> i33 {
^entry:
  %r: i33 = call @makes %a @0
  %one: i33 = const 1 @0
  %s: i33 = add %r, %one @0
  ret %s @0
}

func @zero(%a: i33) -> i33 {
^entry:
  %z: i33 = const 0 @0
  ret %z @0
}

func @ignores(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = call @zero %p @0
  ret %r @0
}

func @branches(%a: i33) -> i33 {
^entry:
  %z: i33 = const 0 @0
  %c: i1 = icmp eq %a, %z @0
  cond_br %c, ^yes, ^no @0
^yes:
  %one: i33 = const 1 @0
  ret %one @0
^no:
  ret %a @0
}

func @branches_on(%a: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = call @branches %p @0
  ret %r @0
}

func @div(%a: i33, %b: i33) -> i33 {
^entry:
  %q: i33 = udiv %a, %b @0
  ret %q @0
}

func @calls_div(%a: i33, %b: i33) -> i33 {
^entry:
  %q: i33 = call @div %a, %b @0
  ret %q @0
}

locs {
  @0 = unknown
}
