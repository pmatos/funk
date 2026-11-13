func @frem(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = frem %a, %b @0
  ret %r @0
}

func @fmod(%a: f16, %b: f16) -> f16 {
^entry:
  %r: f16 = fmod %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
