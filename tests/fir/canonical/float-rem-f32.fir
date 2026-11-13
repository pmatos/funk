func @frem(%a: f32, %b: f32) -> f32 {
^entry:
  %r: f32 = frem %a, %b @0
  ret %r @0
}

func @fmod(%a: f32, %b: f32) -> f32 {
^entry:
  %r: f32 = fmod %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
