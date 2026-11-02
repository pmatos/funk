func @select_form(%a: i1, %b: i1, %x: i8, %y: i8) -> i8 {
^entry:
  %c: i1 = add nsw %a, %b @0
  %s: i8 = select %c, %x, %y @0
  ret %s @0
}

func @cond_br_form(%a: i1, %b: i1, %x: i8, %y: i8) -> i8 {
^entry:
  %c: i1 = add nsw %a, %b @0
  cond_br %c, ^join(%x), ^join(%y) @0
^join(%s: i8):
  ret %s @0
}

func @frozen_cond_br_form(%a: i1, %b: i1, %x: i8, %y: i8) -> i8 {
^entry:
  %c: i1 = add nsw %a, %b @0
  %f: i1 = freeze %c @0
  cond_br %f, ^join(%x), ^join(%y) @0
^join(%s: i8):
  ret %s @0
}

locs {
  @0 = unknown
}
