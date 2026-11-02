func @get0(%b0: i1, %b1: i8, %b2: i16, %b3: i32, %b4: i64, %b5: i1, %b6: i8, %b7: i16, %b8: i32, %b9: i64) -> i1 {
^entry:
  ret %b0 @0
}

func @get1(%b0: i1, %b1: i8, %b2: i16, %b3: i32, %b4: i64, %b5: i1, %b6: i8, %b7: i16, %b8: i32, %b9: i64) -> i8 {
^entry:
  ret %b1 @0
}

func @get2(%b0: i1, %b1: i8, %b2: i16, %b3: i32, %b4: i64, %b5: i1, %b6: i8, %b7: i16, %b8: i32, %b9: i64) -> i16 {
^entry:
  ret %b2 @0
}

func @get3(%b0: i1, %b1: i8, %b2: i16, %b3: i32, %b4: i64, %b5: i1, %b6: i8, %b7: i16, %b8: i32, %b9: i64) -> i32 {
^entry:
  ret %b3 @0
}

func @get4(%b0: i1, %b1: i8, %b2: i16, %b3: i32, %b4: i64, %b5: i1, %b6: i8, %b7: i16, %b8: i32, %b9: i64) -> i64 {
^entry:
  ret %b4 @0
}

func @get5(%b0: i1, %b1: i8, %b2: i16, %b3: i32, %b4: i64, %b5: i1, %b6: i8, %b7: i16, %b8: i32, %b9: i64) -> i1 {
^entry:
  ret %b5 @0
}

func @get6(%b0: i1, %b1: i8, %b2: i16, %b3: i32, %b4: i64, %b5: i1, %b6: i8, %b7: i16, %b8: i32, %b9: i64) -> i8 {
^entry:
  ret %b6 @0
}

func @get7(%b0: i1, %b1: i8, %b2: i16, %b3: i32, %b4: i64, %b5: i1, %b6: i8, %b7: i16, %b8: i32, %b9: i64) -> i16 {
^entry:
  ret %b7 @0
}

func @get8(%b0: i1, %b1: i8, %b2: i16, %b3: i32, %b4: i64, %b5: i1, %b6: i8, %b7: i16, %b8: i32, %b9: i64) -> i32 {
^entry:
  ret %b8 @0
}

func @get9(%b0: i1, %b1: i8, %b2: i16, %b3: i32, %b4: i64, %b5: i1, %b6: i8, %b7: i16, %b8: i32, %b9: i64) -> i64 {
^entry:
  ret %b9 @0
}

func @add_i1(%b0: i1, %b1: i8, %b2: i16, %b3: i32, %b4: i64, %b5: i1, %b6: i8, %b7: i16, %b8: i32, %b9: i64) -> i1 {
^entry:
  %s: i1 = add %b0, %b5 @0
  ret %s @0
}

func @add_i8(%b0: i1, %b1: i8, %b2: i16, %b3: i32, %b4: i64, %b5: i1, %b6: i8, %b7: i16, %b8: i32, %b9: i64) -> i8 {
^entry:
  %s: i8 = add %b1, %b6 @0
  ret %s @0
}

func @add_i16(%b0: i1, %b1: i8, %b2: i16, %b3: i32, %b4: i64, %b5: i1, %b6: i8, %b7: i16, %b8: i32, %b9: i64) -> i16 {
^entry:
  %s: i16 = add %b2, %b7 @0
  ret %s @0
}

func @add_i32(%b0: i1, %b1: i8, %b2: i16, %b3: i32, %b4: i64, %b5: i1, %b6: i8, %b7: i16, %b8: i32, %b9: i64) -> i32 {
^entry:
  %s: i32 = add %b3, %b8 @0
  ret %s @0
}

func @add_i64(%b0: i1, %b1: i8, %b2: i16, %b3: i32, %b4: i64, %b5: i1, %b6: i8, %b7: i16, %b8: i32, %b9: i64) -> i64 {
^entry:
  %s: i64 = add %b4, %b9 @0
  ret %s @0
}

locs {
  @0 = unknown
}
