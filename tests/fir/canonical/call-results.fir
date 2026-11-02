func @nothing() {
^entry:
  ret @0
}

func @call_nothing(%a: i64) -> i64 {
^entry:
  call @nothing @0
  ret %a @0
}

func @sink(%a: i8, %b: i32) {
^entry:
  %s: i8 = add %a, %a @0
  ret @0
}

func @call_sink(%a: i8, %b: i32) -> i32 {
^entry:
  call @sink %a, %b @0
  ret %b @0
}

func @seven() -> i16 {
^entry:
  %c: i16 = const 7 @0
  ret %c @0
}

func @call_seven() -> i16 {
^entry:
  %r: i16 = call @seven @0
  ret %r @0
}

locs {
  @0 = unknown
}
