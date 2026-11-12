func @frem(%a: f64, %b: f64) -> f64 {
^entry:
  %r: f64 = frem %a, %b @0
  ret %r @0
}

func @fmod(%a: f64, %b: f64) -> f64 {
^entry:
  %r: f64 = fmod %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
