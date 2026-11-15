func @round_i1(%v: i1) -> i1 {
^entry:
  %p: ptr = alloca stack i1 @0
  store nonatomic %v, %p @0
  %r: i1 = load nonatomic %p @0
  ret %r @0
}

func @round_i8(%v: i8) -> i8 {
^entry:
  %p: ptr = alloca stack i8 @0
  store nonatomic %v, %p @0
  %r: i8 = load nonatomic %p @0
  ret %r @0
}

func @round_i16(%v: i16) -> i16 {
^entry:
  %p: ptr = alloca stack i16 @0
  store nonatomic %v, %p @0
  %r: i16 = load nonatomic %p @0
  ret %r @0
}

func @round_i32(%v: i32) -> i32 {
^entry:
  %p: ptr = alloca stack i32 @0
  store nonatomic %v, %p @0
  %r: i32 = load nonatomic %p @0
  ret %r @0
}

func @round_i64(%v: i64) -> i64 {
^entry:
  %p: ptr = alloca stack i64 @0
  store nonatomic %v, %p @0
  %r: i64 = load nonatomic %p @0
  ret %r @0
}

func @round_i128(%v: i128) -> i128 {
^entry:
  %p: ptr = alloca stack i128 @0
  store nonatomic %v, %p @0
  %r: i128 = load nonatomic %p @0
  ret %r @0
}

func @by_i1(%k: i1) -> i8 {
^entry:
  %p: ptr = alloca stack i32 @0
  %bytes: i32 = const 67305985 @0
  store nonatomic %bytes, %p @0
  %two: i64 = const 2 @0
  %q: ptr = ptradd %p, %two @0
  %r: ptr = ptradd %q, %k @0
  %w: i8 = load nonatomic %r @0
  ret %w @0
}

func @by_i8(%k: i8) -> i8 {
^entry:
  %p: ptr = alloca stack i32 @0
  %bytes: i32 = const 67305985 @0
  store nonatomic %bytes, %p @0
  %two: i64 = const 2 @0
  %q: ptr = ptradd %p, %two @0
  %r: ptr = ptradd %q, %k @0
  %w: i8 = load nonatomic %r @0
  ret %w @0
}

func @by_i16(%k: i16) -> i8 {
^entry:
  %p: ptr = alloca stack i32 @0
  %bytes: i32 = const 67305985 @0
  store nonatomic %bytes, %p @0
  %two: i64 = const 2 @0
  %q: ptr = ptradd %p, %two @0
  %r: ptr = ptradd %q, %k @0
  %w: i8 = load nonatomic %r @0
  ret %w @0
}

func @by_i32(%k: i32) -> i8 {
^entry:
  %p: ptr = alloca stack i32 @0
  %bytes: i32 = const 67305985 @0
  store nonatomic %bytes, %p @0
  %two: i64 = const 2 @0
  %q: ptr = ptradd %p, %two @0
  %r: ptr = ptradd %q, %k @0
  %w: i8 = load nonatomic %r @0
  ret %w @0
}

func @by_i64(%k: i64) -> i8 {
^entry:
  %p: ptr = alloca stack i32 @0
  %bytes: i32 = const 67305985 @0
  store nonatomic %bytes, %p @0
  %two: i64 = const 2 @0
  %q: ptr = ptradd %p, %two @0
  %r: ptr = ptradd %q, %k @0
  %w: i8 = load nonatomic %r @0
  ret %w @0
}

func @by_i128(%k: i128) -> i8 {
^entry:
  %p: ptr = alloca stack i32 @0
  %bytes: i32 = const 67305985 @0
  store nonatomic %bytes, %p @0
  %two: i64 = const 2 @0
  %q: ptr = ptradd %p, %two @0
  %r: ptr = ptradd %q, %k @0
  %w: i8 = load nonatomic %r @0
  ret %w @0
}

func @pointer(%v: i8) -> i8 {
^entry:
  %x: ptr = alloca stack i8 @0
  %s: ptr = alloca stack ptr @0
  store nonatomic %v, %x @0
  store nonatomic %x, %s @0
  %y: ptr = load nonatomic %s @0
  %w: i8 = load nonatomic %y @0
  ret %w @0
}

func @passes(%n: i32) -> i32, i32 {
^entry:
  %z: i32 = const 0 @0
  %p0: ptr = alloca stack i32 @0
  store nonatomic %z, %p0 @0
  br ^head(%z, %p0) @0
^head(%i: i32, %last: ptr):
  %done: i1 = icmp sge %i, %n @0
  cond_br %done, ^exit, ^body @0
^body:
  %one: i32 = const 1 @0
  %j: i32 = add %i, %one @0
  %q: ptr = alloca stack i32 @0
  store nonatomic %j, %q @0
  br ^head(%j, %q) @0
^exit:
  %first: i32 = load nonatomic %p0 @0
  %end: i32 = load nonatomic %last @0
  ret %first, %end @0
}

locs {
  @0 = unknown
}
