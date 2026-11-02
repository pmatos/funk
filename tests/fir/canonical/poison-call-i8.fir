func @id(%a: i8) -> i8 {
^entry:
  ret %a @0
}

func @passes(%a: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = call @id %p @0
  ret %r @0
}

func @makes(%a: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  ret %p @0
}

func @receives(%a: i8) -> i8 {
^entry:
  %r: i8 = call @makes %a @0
  %one: i8 = const 1 @0
  %s: i8 = add %r, %one @0
  ret %s @0
}

func @zero(%a: i8) -> i8 {
^entry:
  %z: i8 = const 0 @0
  ret %z @0
}

func @ignores(%a: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = call @zero %p @0
  ret %r @0
}

func @branches(%a: i8) -> i8 {
^entry:
  %z: i8 = const 0 @0
  %c: i1 = icmp eq %a, %z @0
  cond_br %c, ^yes, ^no @0
^yes:
  %one: i8 = const 1 @0
  ret %one @0
^no:
  ret %a @0
}

func @branches_on(%a: i8) -> i8 {
^entry:
  %one: i8 = const 1 @0
  %p: i8 = add nsw %a, %one @0
  %r: i8 = call @branches %p @0
  ret %r @0
}

func @div(%a: i8, %b: i8) -> i8 {
^entry:
  %q: i8 = udiv %a, %b @0
  ret %q @0
}

func @calls_div(%a: i8, %b: i8) -> i8 {
^entry:
  %q: i8 = call @div %a, %b @0
  ret %q @0
}

locs {
  @0 = unknown
}
