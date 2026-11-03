func @freeze(%a: i128) -> i128 {
^entry:
  %f: i128 = freeze %a @0
  ret %f @0
}

func @freeze_poison(%a: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %f: i128 = freeze %p @0
  ret %f @0
}

func @freeze_sub(%a: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %f: i128 = freeze %p @0
  %d: i128 = sub %f, %f @0
  ret %d @0
}

func @freeze_twice(%a: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %f: i128 = freeze %p @0
  %g: i128 = freeze %p @0
  %d: i128 = sub %f, %g @0
  ret %d @0
}

func @freeze_halves(%a: i128) -> i128 {
^entry:
  %one: i128 = const 1 @0
  %p: i128 = add nsw %a, %one @0
  %f: i128 = freeze %p @0
  %k: i128 = const 64 @0
  %h: i128 = lshr %f, %k @0
  %g: i128 = shl %f, %k @0
  %l: i128 = lshr %g, %k @0
  %hi: i128 = shl %h, %k @0
  %w: i128 = or %hi, %l @0
  %d: i128 = xor %w, %f @0
  ret %d @0
}

locs {
  @0 = unknown
}
