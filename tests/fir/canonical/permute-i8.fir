func @swap_first(%a: i8, %b: i8, %n: i8) -> i8 {
^entry:
  br ^loop(%a, %b, %n) @0
^loop(%x: i8, %y: i8, %k: i8):
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %k, %zero @0
  cond_br %done, ^exit(%x), ^body @0
^body:
  %one: i8 = const 1 @0
  %k1: i8 = sub %k, %one @0
  br ^loop(%y, %x, %k1) @0
^exit(%r: i8):
  ret %r @0
}

func @swap_second(%a: i8, %b: i8, %n: i8) -> i8 {
^entry:
  br ^loop(%a, %b, %n) @0
^loop(%x: i8, %y: i8, %k: i8):
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %k, %zero @0
  cond_br %done, ^exit(%y), ^body @0
^body:
  %one: i8 = const 1 @0
  %k1: i8 = sub %k, %one @0
  br ^loop(%y, %x, %k1) @0
^exit(%r: i8):
  ret %r @0
}

func @rotate_first(%a: i8, %b: i8, %c: i8, %n: i8) -> i8 {
^entry:
  br ^loop(%a, %b, %c, %n) @0
^loop(%x: i8, %y: i8, %z: i8, %k: i8):
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %k, %zero @0
  cond_br %done, ^exit(%x), ^body @0
^body:
  %one: i8 = const 1 @0
  %k1: i8 = sub %k, %one @0
  br ^loop(%y, %z, %x, %k1) @0
^exit(%r: i8):
  ret %r @0
}

func @rotate_second(%a: i8, %b: i8, %c: i8, %n: i8) -> i8 {
^entry:
  br ^loop(%a, %b, %c, %n) @0
^loop(%x: i8, %y: i8, %z: i8, %k: i8):
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %k, %zero @0
  cond_br %done, ^exit(%y), ^body @0
^body:
  %one: i8 = const 1 @0
  %k1: i8 = sub %k, %one @0
  br ^loop(%y, %z, %x, %k1) @0
^exit(%r: i8):
  ret %r @0
}

func @rotate_third(%a: i8, %b: i8, %c: i8, %n: i8) -> i8 {
^entry:
  br ^loop(%a, %b, %c, %n) @0
^loop(%x: i8, %y: i8, %z: i8, %k: i8):
  %zero: i8 = const 0 @0
  %done: i1 = icmp eq %k, %zero @0
  cond_br %done, ^exit(%z), ^body @0
^body:
  %one: i8 = const 1 @0
  %k1: i8 = sub %k, %one @0
  br ^loop(%y, %z, %x, %k1) @0
^exit(%r: i8):
  ret %r @0
}

locs {
  @0 = unknown
}
