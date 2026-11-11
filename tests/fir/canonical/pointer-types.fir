func @id(%p: ptr) -> ptr {
^entry:
  ret %p @0
}

func @mixed(%a: i32, %p: ptr, %x: f64) -> f64, ptr, i32 {
^entry:
  ret %x, %p, %a @0
}

func @pass(%c: i1, %p: ptr, %q: ptr) -> ptr {
^entry:
  cond_br %c, ^left(%p), ^right(%q) @0
^left(%l: ptr):
  br ^join(%l) @0
^right(%r: ptr):
  br ^join(%r) @0
^join(%j: ptr):
  ret %j @0
}

func @call(%p: ptr, %a: i8) -> i8, ptr {
^entry:
  %q: ptr = call @id %p @0
  ret %a, %q @0
}

func @drop(%p: ptr) -> i8 {
^entry:
  %c: i8 = const 7 @0
  ret %c @0
}

locs {
  @0 = unknown
}
