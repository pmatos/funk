func @add(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = add %a, %b @0
  ret %r @0
}

func @add_nsw(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = add nsw %a, %b @0
  ret %r @0
}

func @sub_self(%a: i8) -> i8 {
^entry:
  %r: i8 = sub %a, %a @0
  ret %r @0
}

func @mul_zero(%a: i8) -> i8 {
^entry:
  %k: i8 = const 0 @0
  %r: i8 = mul %a, %k @0
  ret %r @0
}

func @and_zero(%a: i8) -> i8 {
^entry:
  %k: i8 = const 0 @0
  %r: i8 = and %a, %k @0
  ret %r @0
}

func @or_ones(%a: i8) -> i8 {
^entry:
  %k: i8 = const -1 @0
  %r: i8 = or %a, %k @0
  ret %r @0
}

func @xor_self(%a: i8) -> i8 {
^entry:
  %r: i8 = xor %a, %a @0
  ret %r @0
}

func @shl(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = shl %a, %b @0
  ret %r @0
}

func @lshr(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = lshr %a, %b @0
  ret %r @0
}

func @ashr(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = ashr %a, %b @0
  ret %r @0
}

func @icmp_eq_self(%a: i8) -> i1 {
^entry:
  %r: i1 = icmp eq %a, %a @0
  ret %r @0
}

func @icmp_ult(%a: i8, %b: i8) -> i1 {
^entry:
  %r: i1 = icmp ult %a, %b @0
  ret %r @0
}

func @select(%c: i1, %a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = select %c, %a, %b @0
  ret %r @0
}

func @zext(%a: i8) -> i16 {
^entry:
  %r: i16 = zext %a @0
  ret %r @0
}

func @sext(%a: i8) -> i16 {
^entry:
  %r: i16 = sext %a @0
  ret %r @0
}

func @trunc(%a: i8) -> i1 {
^entry:
  %r: i1 = trunc %a @0
  ret %r @0
}

func @udiv(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = udiv %a, %b @0
  ret %r @0
}

func @sdiv(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = sdiv %a, %b @0
  ret %r @0
}

func @urem(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = urem %a, %b @0
  ret %r @0
}

func @srem(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = srem %a, %b @0
  ret %r @0
}

func @br_arg(%a: i8) -> i8 {
^entry:
  br ^next(%a) @0
^next(%x: i8):
  ret %x @0
}

func @cond_br(%c: i1, %a: i8, %b: i8) -> i8 {
^entry:
  cond_br %c, ^left(%a), ^right(%b) @0
^left(%x: i8):
  ret %x @0
^right(%y: i8):
  ret %y @0
}

func @loop(%n: i8, %x: i8) -> i8 {
^entry:
  br ^loop(%n, %x) @0
^loop(%i: i8, %v: i8):
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %i, %zero @0
  cond_br %done, ^exit(%v), ^body @0
^body:
  %one: i8 = const 1 @0
  %next: i8 = sub %i, %one @0
  br ^loop(%next, %v) @0
^exit(%r: i8):
  ret %r @0
}

func @id(%a: i8) -> i8 {
^entry:
  ret %a @0
}

func @call_id(%a: i8) -> i8 {
^entry:
  %r: i8 = call @id %a @0
  ret %r @0
}

func @first(%a: i8, %b: i8) -> i8 {
^entry:
  ret %a @0
}

func @call_first(%a: i8, %b: i8) -> i8 {
^entry:
  %r: i8 = call @first %a, %b @0
  ret %r @0
}

func @rec(%n: i8, %x: i8) -> i8 {
^entry:
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^exit, ^body @0
^exit:
  ret %x @0
^body:
  %one: i8 = const 1 @0
  %m: i8 = sub %n, %one @0
  %r: i8 = call @rec %m, %x @0
  ret %r @0
}

func @swap(%a: i8, %b: i8) -> i8, i8 {
^entry:
  ret %b, %a @0
}

func @call_swap(%a: i8, %b: i8) -> i8, i8 {
^entry:
  %x: i8, %y: i8 = call @swap %a, %b @0
  ret %x, %y @0
}

func @freeze_sub(%a: i8) -> i8 {
^entry:
  %f: i8 = freeze %a @0
  %r: i8 = sub %f, %f @0
  ret %r @0
}

locs {
  @0 = unknown
}
