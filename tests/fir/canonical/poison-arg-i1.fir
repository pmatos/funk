func @add(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = add %a, %b @0
  ret %r @0
}

func @add_nsw(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = add nsw %a, %b @0
  ret %r @0
}

func @sub_self(%a: i1) -> i1 {
^entry:
  %r: i1 = sub %a, %a @0
  ret %r @0
}

func @mul_zero(%a: i1) -> i1 {
^entry:
  %k: i1 = const false @0
  %r: i1 = mul %a, %k @0
  ret %r @0
}

func @and_zero(%a: i1) -> i1 {
^entry:
  %k: i1 = const false @0
  %r: i1 = and %a, %k @0
  ret %r @0
}

func @or_ones(%a: i1) -> i1 {
^entry:
  %k: i1 = const true @0
  %r: i1 = or %a, %k @0
  ret %r @0
}

func @xor_self(%a: i1) -> i1 {
^entry:
  %r: i1 = xor %a, %a @0
  ret %r @0
}

func @shl(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = shl %a, %b @0
  ret %r @0
}

func @lshr(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = lshr %a, %b @0
  ret %r @0
}

func @ashr(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = ashr %a, %b @0
  ret %r @0
}

func @icmp_eq_self(%a: i1) -> i1 {
^entry:
  %r: i1 = icmp eq %a, %a @0
  ret %r @0
}

func @icmp_ult(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = icmp ult %a, %b @0
  ret %r @0
}

func @select(%c: i1, %a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = select %c, %a, %b @0
  ret %r @0
}

func @zext(%a: i1) -> i8 {
^entry:
  %r: i8 = zext %a @0
  ret %r @0
}

func @sext(%a: i1) -> i8 {
^entry:
  %r: i8 = sext %a @0
  ret %r @0
}

func @trunc(%a: i8) -> i1 {
^entry:
  %r: i1 = trunc %a @0
  ret %r @0
}

func @udiv(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = udiv %a, %b @0
  ret %r @0
}

func @sdiv(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = sdiv %a, %b @0
  ret %r @0
}

func @urem(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = urem %a, %b @0
  ret %r @0
}

func @srem(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = srem %a, %b @0
  ret %r @0
}

func @br_arg(%a: i1) -> i1 {
^entry:
  br ^next(%a) @0
^next(%x: i1):
  ret %x @0
}

func @cond_br(%c: i1, %a: i1, %b: i1) -> i1 {
^entry:
  cond_br %c, ^left(%a), ^right(%b) @0
^left(%x: i1):
  ret %x @0
^right(%y: i1):
  ret %y @0
}

func @loop(%n: i8, %x: i1) -> i1 {
^entry:
  br ^loop(%n, %x) @0
^loop(%i: i8, %v: i1):
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %i, %zero @0
  cond_br %done, ^exit(%v), ^body @0
^body:
  %one: i8 = const 1 @0
  %next: i8 = sub %i, %one @0
  br ^loop(%next, %v) @0
^exit(%r: i1):
  ret %r @0
}

func @id(%a: i1) -> i1 {
^entry:
  ret %a @0
}

func @call_id(%a: i1) -> i1 {
^entry:
  %r: i1 = call @id %a @0
  ret %r @0
}

func @first(%a: i1, %b: i1) -> i1 {
^entry:
  ret %a @0
}

func @call_first(%a: i1, %b: i1) -> i1 {
^entry:
  %r: i1 = call @first %a, %b @0
  ret %r @0
}

func @rec(%n: i8, %x: i1) -> i1 {
^entry:
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^exit, ^body @0
^exit:
  ret %x @0
^body:
  %one: i8 = const 1 @0
  %m: i8 = sub %n, %one @0
  %r: i1 = call @rec %m, %x @0
  ret %r @0
}

func @swap(%a: i1, %b: i1) -> i1, i1 {
^entry:
  ret %b, %a @0
}

func @call_swap(%a: i1, %b: i1) -> i1, i1 {
^entry:
  %x: i1, %y: i1 = call @swap %a, %b @0
  ret %x, %y @0
}

func @freeze_sub(%a: i1) -> i1 {
^entry:
  %f: i1 = freeze %a @0
  %r: i1 = sub %f, %f @0
  ret %r @0
}

locs {
  @0 = unknown
}
