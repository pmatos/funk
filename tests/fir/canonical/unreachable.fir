func @guard_i1(%c: i1, %x: i1) -> i1 {
^entry:
  cond_br %c, ^ok, ^dead @0
^ok:
  ret %x @0
^dead:
  unreachable @0
}

func @guard_i8(%c: i1, %x: i8) -> i8 {
^entry:
  cond_br %c, ^dead, ^ok @0
^dead:
  unreachable @0
^ok:
  ret %x @0
}

func @guard_i16(%c: i1, %x: i16) -> i16 {
^entry:
  cond_br %c, ^ok, ^dead @0
^ok:
  ret %x @0
^dead:
  unreachable @0
}

func @guard_i32(%c: i1, %x: i32) -> i32 {
^entry:
  cond_br %c, ^dead, ^ok @0
^dead:
  unreachable @0
^ok:
  ret %x @0
}

func @guard_i64(%c: i1, %x: i64) -> i64 {
^entry:
  cond_br %c, ^ok, ^dead @0
^ok:
  ret %x @0
^dead:
  unreachable @0
}

func @guard_i128(%c: i1, %x: i128) -> i128 {
^entry:
  cond_br %c, ^dead, ^ok @0
^dead:
  unreachable @0
^ok:
  ret %x @0
}

func @spin() {
^entry:
  br ^loop @0
^loop:
  br ^loop @0
}

func @after_spin(%c: i1, %x: i64) -> i64 {
^entry:
  cond_br %c, ^ok, ^fail @0
^ok:
  ret %x @0
^fail:
  call @spin @0
  unreachable @0
}

func @never() -> i8 {
^entry:
  unreachable @0
}

func @calls_never(%c: i1, %x: i8) -> i8 {
^entry:
  cond_br %c, ^ok, ^bad @0
^ok:
  ret %x @0
^bad:
  %r: i8 = call @never @0
  ret %r @0
}

func @after_ops(%c: i1, %x: i32) -> i32 {
^entry:
  %y: i32 = add %x, %x @0
  cond_br %c, ^ok(%y), ^dead @0
^ok(%r: i32):
  ret %r @0
^dead:
  %z: i32 = mul %y, %x @0
  unreachable @0
}

locs {
  @0 = unknown
}
