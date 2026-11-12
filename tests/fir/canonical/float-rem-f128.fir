func @frem(%a: f128, %b: f128) -> f128 {
^entry:
  %r: f128 = frem %a, %b @0
  ret %r @0
}

func @fmod(%a: f128, %b: f128) -> f128 {
^entry:
  %r: f128 = fmod %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
