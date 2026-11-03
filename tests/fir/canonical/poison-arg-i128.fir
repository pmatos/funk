func @add(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = add %a, %b @0
  ret %r @0
}

func @add_nsw(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = add nsw %a, %b @0
  ret %r @0
}

func @sub_self(%a: i128) -> i128 {
^entry:
  %r: i128 = sub %a, %a @0
  ret %r @0
}

func @mul_zero(%a: i128) -> i128 {
^entry:
  %k: i128 = const 0 @0
  %r: i128 = mul %a, %k @0
  ret %r @0
}

func @and_zero(%a: i128) -> i128 {
^entry:
  %k: i128 = const 0 @0
  %r: i128 = and %a, %k @0
  ret %r @0
}

func @or_ones(%a: i128) -> i128 {
^entry:
  %k: i128 = const -1 @0
  %r: i128 = or %a, %k @0
  ret %r @0
}

func @xor_self(%a: i128) -> i128 {
^entry:
  %r: i128 = xor %a, %a @0
  ret %r @0
}

func @shl(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = shl %a, %b @0
  ret %r @0
}

func @lshr(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = lshr %a, %b @0
  ret %r @0
}

func @ashr(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = ashr %a, %b @0
  ret %r @0
}

func @icmp_eq_self(%a: i128) -> i1 {
^entry:
  %r: i1 = icmp eq %a, %a @0
  ret %r @0
}

func @icmp_ult(%a: i128, %b: i128) -> i1 {
^entry:
  %r: i1 = icmp ult %a, %b @0
  ret %r @0
}

func @select(%c: i1, %a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = select %c, %a, %b @0
  ret %r @0
}

func @zext(%a: i64) -> i128 {
^entry:
  %r: i128 = zext %a @0
  ret %r @0
}

func @sext(%a: i64) -> i128 {
^entry:
  %r: i128 = sext %a @0
  ret %r @0
}

func @trunc(%a: i128) -> i1 {
^entry:
  %r: i1 = trunc %a @0
  ret %r @0
}

func @udiv(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = udiv %a, %b @0
  ret %r @0
}

func @sdiv(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = sdiv %a, %b @0
  ret %r @0
}

func @urem(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = urem %a, %b @0
  ret %r @0
}

func @srem(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = srem %a, %b @0
  ret %r @0
}

func @br_arg(%a: i128) -> i128 {
^entry:
  br ^next(%a) @0
^next(%x: i128):
  ret %x @0
}

func @cond_br(%c: i1, %a: i128, %b: i128) -> i128 {
^entry:
  cond_br %c, ^left(%a), ^right(%b) @0
^left(%x: i128):
  ret %x @0
^right(%y: i128):
  ret %y @0
}

func @loop(%n: i8, %x: i128) -> i128 {
^entry:
  br ^loop(%n, %x) @0
^loop(%i: i8, %v: i128):
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %i, %zero @0
  cond_br %done, ^exit(%v), ^body @0
^body:
  %one: i8 = const 1 @0
  %next: i8 = sub %i, %one @0
  br ^loop(%next, %v) @0
^exit(%r: i128):
  ret %r @0
}

func @id(%a: i128) -> i128 {
^entry:
  ret %a @0
}

func @call_id(%a: i128) -> i128 {
^entry:
  %r: i128 = call @id %a @0
  ret %r @0
}

func @first(%a: i128, %b: i128) -> i128 {
^entry:
  ret %a @0
}

func @call_first(%a: i128, %b: i128) -> i128 {
^entry:
  %r: i128 = call @first %a, %b @0
  ret %r @0
}

func @rec(%n: i8, %x: i128) -> i128 {
^entry:
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^exit, ^body @0
^exit:
  ret %x @0
^body:
  %one: i8 = const 1 @0
  %m: i8 = sub %n, %one @0
  %r: i128 = call @rec %m, %x @0
  ret %r @0
}

func @swap(%a: i128, %b: i128) -> i128, i128 {
^entry:
  ret %b, %a @0
}

func @call_swap(%a: i128, %b: i128) -> i128, i128 {
^entry:
  %x: i128, %y: i128 = call @swap %a, %b @0
  ret %x, %y @0
}

func @freeze_sub(%a: i128) -> i128 {
^entry:
  %f: i128 = freeze %a @0
  %r: i128 = sub %f, %f @0
  ret %r @0
}

locs {
  @0 = unknown
}
