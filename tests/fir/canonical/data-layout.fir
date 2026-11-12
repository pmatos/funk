layout memory(1, unit(8), pointer(32), little), memory(2, unit(16), pointer(64), little, align(4), nonintegral)

func @id1(%p: ptr(1)) -> ptr(1) {
^entry:
  ret %p @0
}

func @pick(%c: i1, %p: ptr(2), %q: ptr(2)) -> ptr(2) {
^entry:
  cond_br %c, ^left(%p), ^right(%q) @0
^left(%l: ptr(2)):
  ret %l @0
^right(%r: ptr(2)):
  ret %r @0
}

func @mixed(%a: i8, %p: ptr, %q: ptr(1)) -> ptr(1), i8 {
^entry:
  %r: ptr(1) = call @id1 %q @0
  ret %r, %a @0
}

locs {
  @0 = unknown
}
