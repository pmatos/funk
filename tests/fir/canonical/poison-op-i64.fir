func @poison() -> i64 {
^entry:
  %p: i64 = poison @0
  ret %p @0
}

func @poison_unused(%a: i64) -> i64 {
^entry:
  %p: i64 = poison @0
  ret %a @0
}

func @poison_add(%a: i64) -> i64 {
^entry:
  %p: i64 = poison @0
  %s: i64 = add %a, %p @0
  ret %s @0
}

func @poison_select(%c: i1, %a: i64) -> i64 {
^entry:
  %p: i64 = poison @0
  %s: i64 = select %c, %p, %a @0
  ret %s @0
}

func @poison_icmp() -> i1 {
^entry:
  %p: i64 = poison @0
  %e: i1 = icmp eq %p, %p @0
  ret %e @0
}

func @poison_freeze() -> i64 {
^entry:
  %p: i64 = poison @0
  %f: i64 = freeze %p @0
  ret %f @0
}

func @poison_freeze_sub() -> i64 {
^entry:
  %p: i64 = poison @0
  %f: i64 = freeze %p @0
  %d: i64 = sub %f, %f @0
  ret %d @0
}

func @poison_pair(%a: i64) -> i64, i64 {
^entry:
  %p: i64 = poison @0
  ret %a, %p @0
}

func @first(%a: i64, %b: i64) -> i64 {
^entry:
  ret %a @0
}

func @poison_call(%a: i64) -> i64 {
^entry:
  %p: i64 = poison @0
  %r: i64 = call @first %a, %p @0
  ret %r @0
}

func @poison_cond_br(%a: i64) -> i64 {
^entry:
  %c: i1 = poison @0
  cond_br %c, ^yes, ^no @0
^yes:
  ret %a @0
^no:
  ret %a @0
}

func @poison_udiv(%a: i64) -> i64 {
^entry:
  %p: i64 = poison @0
  %q: i64 = udiv %a, %p @0
  ret %q @0
}

locs {
  @0 = unknown
}
