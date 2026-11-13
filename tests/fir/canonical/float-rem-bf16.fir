func @frem(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = frem %a, %b @0
  ret %r @0
}

func @fmod(%a: bf16, %b: bf16) -> bf16 {
^entry:
  %r: bf16 = fmod %a, %b @0
  ret %r @0
}

locs {
  @0 = unknown
}
