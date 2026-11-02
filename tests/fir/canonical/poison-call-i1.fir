func @id(%a: i1) -> i1 {
^entry:
  ret %a @0
}

func @passes(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = call @id %p @0
  ret %r @0
}

func @makes(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  ret %p @0
}

func @receives(%a: i1) -> i1 {
^entry:
  %r: i1 = call @makes %a @0
  %one: i1 = const true @0
  %s: i1 = add %r, %one @0
  ret %s @0
}

func @zero(%a: i1) -> i1 {
^entry:
  %z: i1 = const false @0
  ret %z @0
}

func @ignores(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = call @zero %p @0
  ret %r @0
}

func @branches(%a: i1) -> i1 {
^entry:
  %z: i1 = const false @0
  %c: i1 = icmp eq %a, %z @0
  cond_br %c, ^yes, ^no @0
^yes:
  %one: i1 = const true @0
  ret %one @0
^no:
  ret %a @0
}

func @branches_on(%a: i1) -> i1 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %a, %one @0
  %r: i1 = call @branches %p @0
  ret %r @0
}

func @div(%a: i1, %b: i1) -> i1 {
^entry:
  %q: i1 = udiv %a, %b @0
  ret %q @0
}

func @calls_div(%a: i1, %b: i1) -> i1 {
^entry:
  %q: i1 = call @div %a, %b @0
  ret %q @0
}

locs {
  @0 = unknown
}
