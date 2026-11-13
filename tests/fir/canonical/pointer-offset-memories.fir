layout memory(1, unit(16), pointer(32), little), memory(2, unit(32), pointer(64), little, align(2), nonintegral)

func @in_one(%p: ptr(1), %k: i16) -> ptr(1) {
^entry:
  %q: ptr(1) = ptradd %p, %k @0
  ret %q @0
}

func @in_two(%p: ptr(2), %k: i64) -> ptr(2) {
^entry:
  %q: ptr(2) = ptradd %p, %k @0
  ret %q @0
}

func @in_each(%a: ptr, %b: ptr(1), %c: ptr(2), %k: i32) -> ptr(2), ptr(1), ptr {
^entry:
  %x: ptr = ptradd %a, %k @0
  %y: ptr(1) = ptradd %b, %k @0
  %z: ptr(2) = ptradd %c, %k @0
  ret %z, %y, %x @0
}

locs {
  @0 = unknown
}
