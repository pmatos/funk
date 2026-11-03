func @add(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = add %a, %b @0
  ret %r @0
}

func @add_nsw(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = add nsw %a, %b @0
  ret %r @0
}

func @sub_self(%a: i32) -> i32 {
^entry:
  %r: i32 = sub %a, %a @0
  ret %r @0
}

func @mul_zero(%a: i32) -> i32 {
^entry:
  %k: i32 = const 0 @0
  %r: i32 = mul %a, %k @0
  ret %r @0
}

func @and_zero(%a: i32) -> i32 {
^entry:
  %k: i32 = const 0 @0
  %r: i32 = and %a, %k @0
  ret %r @0
}

func @or_ones(%a: i32) -> i32 {
^entry:
  %k: i32 = const -1 @0
  %r: i32 = or %a, %k @0
  ret %r @0
}

func @xor_self(%a: i32) -> i32 {
^entry:
  %r: i32 = xor %a, %a @0
  ret %r @0
}

func @shl(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = shl %a, %b @0
  ret %r @0
}

func @lshr(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = lshr %a, %b @0
  ret %r @0
}

func @ashr(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = ashr %a, %b @0
  ret %r @0
}

func @icmp_eq_self(%a: i32) -> i1 {
^entry:
  %r: i1 = icmp eq %a, %a @0
  ret %r @0
}

func @icmp_ult(%a: i32, %b: i32) -> i1 {
^entry:
  %r: i1 = icmp ult %a, %b @0
  ret %r @0
}

func @select(%c: i1, %a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = select %c, %a, %b @0
  ret %r @0
}

func @zext(%a: i32) -> i64 {
^entry:
  %r: i64 = zext %a @0
  ret %r @0
}

func @sext(%a: i32) -> i64 {
^entry:
  %r: i64 = sext %a @0
  ret %r @0
}

func @trunc(%a: i32) -> i1 {
^entry:
  %r: i1 = trunc %a @0
  ret %r @0
}

func @udiv(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = udiv %a, %b @0
  ret %r @0
}

func @sdiv(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = sdiv %a, %b @0
  ret %r @0
}

func @urem(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = urem %a, %b @0
  ret %r @0
}

func @srem(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = srem %a, %b @0
  ret %r @0
}

func @br_arg(%a: i32) -> i32 {
^entry:
  br ^next(%a) @0
^next(%x: i32):
  ret %x @0
}

func @cond_br(%c: i1, %a: i32, %b: i32) -> i32 {
^entry:
  cond_br %c, ^left(%a), ^right(%b) @0
^left(%x: i32):
  ret %x @0
^right(%y: i32):
  ret %y @0
}

func @loop(%n: i8, %x: i32) -> i32 {
^entry:
  br ^loop(%n, %x) @0
^loop(%i: i8, %v: i32):
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %i, %zero @0
  cond_br %done, ^exit(%v), ^body @0
^body:
  %one: i8 = const 1 @0
  %next: i8 = sub %i, %one @0
  br ^loop(%next, %v) @0
^exit(%r: i32):
  ret %r @0
}

func @id(%a: i32) -> i32 {
^entry:
  ret %a @0
}

func @call_id(%a: i32) -> i32 {
^entry:
  %r: i32 = call @id %a @0
  ret %r @0
}

func @first(%a: i32, %b: i32) -> i32 {
^entry:
  ret %a @0
}

func @call_first(%a: i32, %b: i32) -> i32 {
^entry:
  %r: i32 = call @first %a, %b @0
  ret %r @0
}

func @rec(%n: i8, %x: i32) -> i32 {
^entry:
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %n, %zero @0
  cond_br %done, ^exit, ^body @0
^exit:
  ret %x @0
^body:
  %one: i8 = const 1 @0
  %m: i8 = sub %n, %one @0
  %r: i32 = call @rec %m, %x @0
  ret %r @0
}

func @swap(%a: i32, %b: i32) -> i32, i32 {
^entry:
  ret %b, %a @0
}

func @call_swap(%a: i32, %b: i32) -> i32, i32 {
^entry:
  %x: i32, %y: i32 = call @swap %a, %b @0
  ret %x, %y @0
}

func @freeze_sub(%a: i32) -> i32 {
^entry:
  %f: i32 = freeze %a @0
  %r: i32 = sub %f, %f @0
  ret %r @0
}

locs {
  @0 = unknown
}
