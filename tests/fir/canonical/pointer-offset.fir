func @by_i1(%p: ptr, %k: i1) -> ptr {
^entry:
  %q: ptr = ptradd %p, %k @0
  ret %q @0
}

func @by_i7(%p: ptr, %k: i7) -> ptr {
^entry:
  %q: ptr = ptradd %p, %k @0
  ret %q @0
}

func @by_i8(%p: ptr, %k: i8) -> ptr {
^entry:
  %q: ptr = ptradd %p, %k @0
  ret %q @0
}

func @by_i16(%p: ptr, %k: i16) -> ptr {
^entry:
  %q: ptr = ptradd %p, %k @0
  ret %q @0
}

func @by_i32(%p: ptr, %k: i32) -> ptr {
^entry:
  %q: ptr = ptradd %p, %k @0
  ret %q @0
}

func @by_i33(%p: ptr, %k: i33) -> ptr {
^entry:
  %q: ptr = ptradd %p, %k @0
  ret %q @0
}

func @by_i64(%p: ptr, %k: i64) -> ptr {
^entry:
  %q: ptr = ptradd %p, %k @0
  ret %q @0
}

func @by_i128(%p: ptr, %k: i128) -> ptr {
^entry:
  %q: ptr = ptradd %p, %k @0
  ret %q @0
}

func @there_and_back(%p: ptr, %k: i64) -> ptr {
^entry:
  %q: ptr = ptradd %p, %k @0
  %z: i64 = const 0 @0
  %n: i64 = sub %z, %k @0
  %r: ptr = ptradd %q, %n @0
  ret %r @0
}

func @through_call(%p: ptr, %k: i8) -> ptr, i8 {
^entry:
  %q: ptr = call @by_i8 %p, %k @0
  ret %q, %k @0
}

locs {
  @0 = unknown
}
