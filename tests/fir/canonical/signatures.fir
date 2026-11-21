func @widen(%c: i8 sext, %b: i1 zext, %h: i16 zext, %n: i32) -> i8 zext, i16 sext, i32 {
^entry:
  %b8: i8 = zext %b @0
  %s: i8 = add %c, %b8 @0
  %h2: i16 = add %h, %h @0
  ret %s, %h2, %n @0
}

func @caller(%x: i8) -> i8 zext {
^entry:
  %t: i1 = const true @0
  %h: i16 = const 300 @0
  %n: i32 = const 7 @0
  %r: i8, %q: i16, %m: i32 = call @widen %x, %t, %h, %n @0
  ret %r @0
}

func @last(%a: i32, %f: i1 sext) -> i1 sext {
^entry:
  ret %f @0
}

locs {
  @0 = unknown
}
