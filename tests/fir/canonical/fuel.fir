func @spin() {
^entry:
  br ^loop @0
^loop:
  br ^loop @0
}

func @count_up(%a: i8) {
^entry:
  br ^loop(%a) @0
^loop(%i: i8):
  %one: i8 = const 1 @0
  %j: i8 = add %i, %one @0
  br ^loop(%j) @0
}

locs {
  @0 = unknown
}
