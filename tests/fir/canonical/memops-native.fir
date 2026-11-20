func @copy_ptr(%v: i32) -> i32 {
^entry:
  %a: ptr = alloca stack i32 @0
  store nonatomic %v, %a @0
  %s: ptr = alloca stack ptr 2 @0
  store nonatomic %a, %s @0
  %eight: i64 = const 8 @0
  %t: ptr = ptradd %s, %eight @0
  memcpy nonatomic %t, %s, %eight @0
  %b: ptr = load nonatomic %t @0
  %w: i32 = load nonatomic %b @0
  ret %w @0
}

func @move_ptr(%v: i32) -> i32 {
^entry:
  %a: ptr = alloca stack i32 @1
  store nonatomic %v, %a @1
  %s: ptr = alloca stack ptr 3 @1
  store nonatomic %a, %s @1
  %four: i64 = const 4 @1
  %t: ptr = ptradd %s, %four @1
  %n: i64 = const 16 @1
  memmove nonatomic %t, %s, %n @1
  %b: ptr = load nonatomic align(1) %t @1
  %w: i32 = load nonatomic %b @1
  ret %w @1
}

func @copy_i1(%v: i64, %n: i1) -> i64 {
^entry:
  %p: ptr = alloca stack i64 2 @2
  store nonatomic %v, %p @2
  %eight: i64 = const 8 @2
  %q: ptr = ptradd %p, %eight @2
  %zero: i64 = const 0 @2
  store nonatomic %zero, %q @2
  memcpy nonatomic %q, %p, %n @2
  memcpy nonatomic %p, %p, %n @2
  %w: i64 = load nonatomic %q @2
  ret %w @2
}

func @copy_i8(%v: i64, %n: i8) -> i64 {
^entry:
  %p: ptr = alloca stack i64 2 @3
  store nonatomic %v, %p @3
  %eight: i64 = const 8 @3
  %q: ptr = ptradd %p, %eight @3
  %zero: i64 = const 0 @3
  store nonatomic %zero, %q @3
  memcpy nonatomic %q, %p, %n @3
  memcpy nonatomic %p, %p, %n @3
  %w: i64 = load nonatomic %q @3
  ret %w @3
}

func @copy_i16(%v: i64, %n: i16) -> i64 {
^entry:
  %p: ptr = alloca stack i64 2 @4
  store nonatomic %v, %p @4
  %eight: i64 = const 8 @4
  %q: ptr = ptradd %p, %eight @4
  %zero: i64 = const 0 @4
  store nonatomic %zero, %q @4
  memcpy nonatomic %q, %p, %n @4
  memcpy nonatomic %p, %p, %n @4
  %w: i64 = load nonatomic %q @4
  ret %w @4
}

func @copy_i32(%v: i64, %n: i32) -> i64 {
^entry:
  %p: ptr = alloca stack i64 2 @5
  store nonatomic %v, %p @5
  %eight: i64 = const 8 @5
  %q: ptr = ptradd %p, %eight @5
  %zero: i64 = const 0 @5
  store nonatomic %zero, %q @5
  memcpy nonatomic %q, %p, %n @5
  memcpy nonatomic %p, %p, %n @5
  %w: i64 = load nonatomic %q @5
  ret %w @5
}

func @copy_i64(%v: i64, %n: i64) -> i64 {
^entry:
  %p: ptr = alloca stack i64 2 @6
  store nonatomic %v, %p @6
  %eight: i64 = const 8 @6
  %q: ptr = ptradd %p, %eight @6
  %zero: i64 = const 0 @6
  store nonatomic %zero, %q @6
  memcpy nonatomic %q, %p, %n @6
  memcpy nonatomic %p, %p, %n @6
  %w: i64 = load nonatomic %q @6
  ret %w @6
}

func @copy_i128(%v: i64, %n: i128) -> i64 {
^entry:
  %p: ptr = alloca stack i64 2 @7
  store nonatomic %v, %p @7
  %eight: i64 = const 8 @7
  %q: ptr = ptradd %p, %eight @7
  %zero: i64 = const 0 @7
  store nonatomic %zero, %q @7
  memcpy nonatomic %q, %p, %n @7
  memcpy nonatomic %p, %p, %n @7
  %w: i64 = load nonatomic %q @7
  ret %w @7
}

func @move_i1(%v: i64, %k: i64, %n: i1) -> i64 {
^entry:
  %p: ptr = alloca stack i64 2 @8
  %zero: i64 = const 0 @8
  store nonatomic %zero, %p @8
  %eight: i64 = const 8 @8
  %h: ptr = ptradd %p, %eight @8
  store nonatomic %zero, %h @8
  %four: i64 = const 4 @8
  %s: ptr = ptradd %p, %four @8
  store nonatomic align(1) %v, %s @8
  %d: ptr = ptradd %s, %k @8
  memmove nonatomic %d, %s, %n @8
  %w: i64 = load nonatomic align(1) %d @8
  ret %w @8
}

func @move_i8(%v: i64, %k: i64, %n: i8) -> i64 {
^entry:
  %p: ptr = alloca stack i64 2 @9
  %zero: i64 = const 0 @9
  store nonatomic %zero, %p @9
  %eight: i64 = const 8 @9
  %h: ptr = ptradd %p, %eight @9
  store nonatomic %zero, %h @9
  %four: i64 = const 4 @9
  %s: ptr = ptradd %p, %four @9
  store nonatomic align(1) %v, %s @9
  %d: ptr = ptradd %s, %k @9
  memmove nonatomic %d, %s, %n @9
  %w: i64 = load nonatomic align(1) %d @9
  ret %w @9
}

func @move_i16(%v: i64, %k: i64, %n: i16) -> i64 {
^entry:
  %p: ptr = alloca stack i64 2 @10
  %zero: i64 = const 0 @10
  store nonatomic %zero, %p @10
  %eight: i64 = const 8 @10
  %h: ptr = ptradd %p, %eight @10
  store nonatomic %zero, %h @10
  %four: i64 = const 4 @10
  %s: ptr = ptradd %p, %four @10
  store nonatomic align(1) %v, %s @10
  %d: ptr = ptradd %s, %k @10
  memmove nonatomic %d, %s, %n @10
  %w: i64 = load nonatomic align(1) %d @10
  ret %w @10
}

func @move_i32(%v: i64, %k: i64, %n: i32) -> i64 {
^entry:
  %p: ptr = alloca stack i64 2 @11
  %zero: i64 = const 0 @11
  store nonatomic %zero, %p @11
  %eight: i64 = const 8 @11
  %h: ptr = ptradd %p, %eight @11
  store nonatomic %zero, %h @11
  %four: i64 = const 4 @11
  %s: ptr = ptradd %p, %four @11
  store nonatomic align(1) %v, %s @11
  %d: ptr = ptradd %s, %k @11
  memmove nonatomic %d, %s, %n @11
  %w: i64 = load nonatomic align(1) %d @11
  ret %w @11
}

func @move_i64(%v: i64, %k: i64, %n: i64) -> i64 {
^entry:
  %p: ptr = alloca stack i64 2 @12
  %zero: i64 = const 0 @12
  store nonatomic %zero, %p @12
  %eight: i64 = const 8 @12
  %h: ptr = ptradd %p, %eight @12
  store nonatomic %zero, %h @12
  %four: i64 = const 4 @12
  %s: ptr = ptradd %p, %four @12
  store nonatomic align(1) %v, %s @12
  %d: ptr = ptradd %s, %k @12
  memmove nonatomic %d, %s, %n @12
  %w: i64 = load nonatomic align(1) %d @12
  ret %w @12
}

func @move_i128(%v: i64, %k: i64, %n: i128) -> i64 {
^entry:
  %p: ptr = alloca stack i64 2 @13
  %zero: i64 = const 0 @13
  store nonatomic %zero, %p @13
  %eight: i64 = const 8 @13
  %h: ptr = ptradd %p, %eight @13
  store nonatomic %zero, %h @13
  %four: i64 = const 4 @13
  %s: ptr = ptradd %p, %four @13
  store nonatomic align(1) %v, %s @13
  %d: ptr = ptradd %s, %k @13
  memmove nonatomic %d, %s, %n @13
  %w: i64 = load nonatomic align(1) %d @13
  ret %w @13
}

func @set_i1(%v: i8, %n: i1) -> i64 {
^entry:
  %p: ptr = alloca stack i64 @14
  %x: i64 = const -1 @14
  store nonatomic %x, %p @14
  memset nonatomic %p, %v, %n @14
  %w: i64 = load nonatomic %p @14
  ret %w @14
}

func @set_i8(%v: i8, %n: i8) -> i64 {
^entry:
  %p: ptr = alloca stack i64 @15
  %x: i64 = const -1 @15
  store nonatomic %x, %p @15
  memset nonatomic %p, %v, %n @15
  %w: i64 = load nonatomic %p @15
  ret %w @15
}

func @set_i16(%v: i8, %n: i16) -> i64 {
^entry:
  %p: ptr = alloca stack i64 @16
  %x: i64 = const -1 @16
  store nonatomic %x, %p @16
  memset nonatomic %p, %v, %n @16
  %w: i64 = load nonatomic %p @16
  ret %w @16
}

func @set_i32(%v: i8, %n: i32) -> i64 {
^entry:
  %p: ptr = alloca stack i64 @17
  %x: i64 = const -1 @17
  store nonatomic %x, %p @17
  memset nonatomic %p, %v, %n @17
  %w: i64 = load nonatomic %p @17
  ret %w @17
}

func @set_i64(%v: i8, %n: i64) -> i64 {
^entry:
  %p: ptr = alloca stack i64 @18
  %x: i64 = const -1 @18
  store nonatomic %x, %p @18
  memset nonatomic %p, %v, %n @18
  %w: i64 = load nonatomic %p @18
  ret %w @18
}

func @set_i128(%v: i8, %n: i128) -> i64 {
^entry:
  %p: ptr = alloca stack i64 @19
  %x: i64 = const -1 @19
  store nonatomic %x, %p @19
  memset nonatomic %p, %v, %n @19
  %w: i64 = load nonatomic %p @19
  ret %w @19
}

func @poison_move(%n: i1) -> i8 {
^entry:
  %p: ptr = alloca stack i8 @20
  %v: i8 = const 7 @20
  store nonatomic %v, %p @20
  memmove nonatomic %p, %p, %n @20
  %w: i8 = load nonatomic %p @20
  ret %w @20
}

func @poison_set(%n: i1) -> i8 {
^entry:
  %p: ptr = alloca stack i8 @21
  %v: i8 = const 7 @21
  store nonatomic %v, %p @21
  %nine: i8 = const 9 @21
  memset nonatomic %p, %nine, %n @21
  %w: i8 = load nonatomic %p @21
  ret %w @21
}

locs {
  @0 = unknown
  @1 = unknown
  @2 = unknown
  @3 = unknown
  @4 = unknown
  @5 = unknown
  @6 = unknown
  @7 = unknown
  @8 = unknown
  @9 = unknown
  @10 = unknown
  @11 = unknown
  @12 = unknown
  @13 = unknown
  @14 = unknown
  @15 = unknown
  @16 = unknown
  @17 = unknown
  @18 = unknown
  @19 = unknown
  @20 = unknown
  @21 = unknown
}
