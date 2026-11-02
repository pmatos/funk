func @select_form(%c: i1, %a: i1, %b: i1) -> i1 {
^entry:
  %x: i1 = add nsw %a, %b @0
  %z: i1 = const false @0
  %s: i1 = select %c, %x, %z @0
  ret %s @0
}

func @and_form(%c: i1, %a: i1, %b: i1) -> i1 {
^entry:
  %x: i1 = add nsw %a, %b @0
  %s: i1 = and %c, %x @0
  ret %s @0
}

func @frozen_and_form(%c: i1, %a: i1, %b: i1) -> i1 {
^entry:
  %x: i1 = add nsw %a, %b @0
  %g: i1 = freeze %x @0
  %s: i1 = and %c, %g @0
  ret %s @0
}

locs {
  @0 = unknown
}
