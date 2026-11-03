func @poison() -> i7 {
^entry:
  %p: i7 = poison @0
  ret %p @0
}

func @poison_unused(%a: i7) -> i7 {
^entry:
  %p: i7 = poison @0
  ret %a @0
}

func @poison_add(%a: i7) -> i7 {
^entry:
  %p: i7 = poison @0
  %s: i7 = add %a, %p @0
  ret %s @0
}

func @poison_select(%c: i1, %a: i7) -> i7 {
^entry:
  %p: i7 = poison @0
  %s: i7 = select %c, %p, %a @0
  ret %s @0
}

func @poison_icmp() -> i1 {
^entry:
  %p: i7 = poison @0
  %e: i1 = icmp eq %p, %p @0
  ret %e @0
}

func @poison_freeze() -> i7 {
^entry:
  %p: i7 = poison @0
  %f: i7 = freeze %p @0
  ret %f @0
}

func @poison_freeze_sub() -> i7 {
^entry:
  %p: i7 = poison @0
  %f: i7 = freeze %p @0
  %d: i7 = sub %f, %f @0
  ret %d @0
}

func @poison_pair(%a: i7) -> i7, i7 {
^entry:
  %p: i7 = poison @0
  ret %a, %p @0
}

func @first(%a: i7, %b: i7) -> i7 {
^entry:
  ret %a @0
}

func @poison_call(%a: i7) -> i7 {
^entry:
  %p: i7 = poison @0
  %r: i7 = call @first %a, %p @0
  ret %r @0
}

func @poison_cond_br(%a: i7) -> i7 {
^entry:
  %c: i1 = poison @0
  cond_br %c, ^yes, ^no @0
^yes:
  ret %a @0
^no:
  ret %a @0
}

func @poison_udiv(%a: i7) -> i7 {
^entry:
  %p: i7 = poison @0
  %q: i7 = udiv %a, %p @0
  ret %q @0
}

locs {
  @0 = unknown
}
