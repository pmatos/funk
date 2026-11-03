func @add(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = add %a, %b @0
  ret %r @0
}

func @add_nsw(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = add nsw %a, %b @0
  ret %r @0
}

func @sub_self(%a: i16) -> i16 {
^entry:
  %r: i16 = sub %a, %a @0
  ret %r @0
}

func @mul_zero(%a: i16) -> i16 {
^entry:
  %k: i16 = const 0 @0
  %r: i16 = mul %a, %k @0
  ret %r @0
}

func @and_zero(%a: i16) -> i16 {
^entry:
  %k: i16 = const 0 @0
  %r: i16 = and %a, %k @0
  ret %r @0
}

func @or_ones(%a: i16) -> i16 {
^entry:
  %k: i16 = const -1 @0
  %r: i16 = or %a, %k @0
  ret %r @0
}

func @xor_self(%a: i16) -> i16 {
^entry:
  %r: i16 = xor %a, %a @0
  ret %r @0
}

func @shl(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = shl %a, %b @0
  ret %r @0
}

func @lshr(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = lshr %a, %b @0
  ret %r @0
}

func @ashr(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = ashr %a, %b @0
  ret %r @0
}

func @icmp_eq_self(%a: i16) -> i1 {
^entry:
  %r: i1 = icmp eq %a, %a @0
  ret %r @0
}

func @icmp_ult(%a: i16, %b: i16) -> i1 {
^entry:
  %r: i1 = icmp ult %a, %b @0
  ret %r @0
}

func @select(%c: i1, %a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = select %c, %a, %b @0
  ret %r @0
}

func @zext(%a: i16) -> i32 {
^entry:
  %r: i32 = zext %a @0
  ret %r @0
}

func @sext(%a: i16) -> i32 {
^entry:
  %r: i32 = sext %a @0
  ret %r @0
}

func @trunc(%a: i16) -> i1 {
^entry:
  %r: i1 = trunc %a @0
  ret %r @0
}

func @udiv(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = udiv %a, %b @0
  ret %r @0
}

func @sdiv(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = sdiv %a, %b @0
  ret %r @0
}

func @urem(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = urem %a, %b @0
  ret %r @0
}

func @srem(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = srem %a, %b @0
  ret %r @0
}

func @br_arg(%a: i16) -> i16 {
^entry:
  br ^next(%a) @0
^next(%x: i16):
  ret %x @0
}

func @cond_br(%c: i1, %a: i16, %b: i16) -> i16 {
^entry:
  cond_br %c, ^left(%a), ^right(%b) @0
^left(%x: i16):
  ret %x @0
^right(%y: i16):
  ret %y @0
}

func @loop(%n: i8, %x: i16) -> i16 {
^entry:
  br ^loop(%n, %x) @0
^loop(%i: i8, %v: i16):
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %i, %zero @0
  cond_br %done, ^exit(%v), ^body @0
^body:
  %one: i8 = const 1 @0
  %next: i8 = sub %i, %one @0
  br ^loop(%next, %v) @0
^exit(%r: i16):
  ret %r @0
}

func @id(%a: i16) -> i16 {
^entry:
  ret %a @0
}

func @call_id(%a: i16) -> i16 {
^entry:
  %r: i16 = call @id %a @0
  ret %r @0
}

func @first(%a: i16, %b: i16) -> i16 {
^entry:
  ret %a @0
}

func @call_first(%a: i16, %b: i16) -> i16 {
^entry:
  %r: i16 = call @first %a, %b @0
  ret %r @0
}

func @rec(%n: i8, %x: i16) -> i16 {
^entry:
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^exit, ^body @0
^exit:
  ret %x @0
^body:
  %one: i8 = const 1 @0
  %m: i8 = sub %n, %one @0
  %r: i16 = call @rec %m, %x @0
  ret %r @0
}

func @swap(%a: i16, %b: i16) -> i16, i16 {
^entry:
  ret %b, %a @0
}

func @call_swap(%a: i16, %b: i16) -> i16, i16 {
^entry:
  %x: i16, %y: i16 = call @swap %a, %b @0
  ret %x, %y @0
}

func @freeze_sub(%a: i16) -> i16 {
^entry:
  %f: i16 = freeze %a @0
  %r: i16 = sub %f, %f @0
  ret %r @0
}

locs {
  @0 = unknown
}
