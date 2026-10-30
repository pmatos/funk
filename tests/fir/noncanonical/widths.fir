func @booleans() -> i1, i1 {
^entry:
  %t: i1 = const true @0
  %f: i1 = const false @0
  ret %t, %f @0
}

func @bytes() -> i8, i8, i8, i8 {
^entry:
  %min: i8 = const-128 @0
  %max: i8 = const 127 @0
  %zero: i8 = const 0 @0
  %ones: i8 = const-1 @0
  ret %min, %max, %zero, %ones @0
}

func @odd(%a: i7, %b: i33) -> i7, i33 {
^entry:
  %c: i7 = const -64 @0
  %d: i7 = add %a, %c @0
  %e: i33 = const 4294967295 @0
  %f: i33 = add %b, %e @0
  ret %d, %f @0
}

func @wide() -> i64, i128, i128 {
^entry:
  %a: i64 = const -9223372036854775808 @0
  %b: i128 = const 170141183460469231731687303715884105727 @0
  %c: i128 = const -170141183460469231731687303715884105728 @0
  ret %a, %b, %c @0
}

func @widest(%x: i16777215) -> i16777215 {
^entry:
  %m: i16777215 = const -1 @0
  %y: i16777215 = add %x, %m @0
  ret %y @0
}

locs { @0 = unknown }
