func @si64(%x: i64, %y: i64) -> i64, i64 {
^entry:
  %r: i64 = sdiv %x, %y @0
  %t: i64 = srem %x, %y @0
  ret %r, %t @0
}

func @si32(%x: i32, %y: i32) -> i32, i32 {
^entry:
  %r: i32 = sdiv %x, %y @1
  %t: i32 = srem %x, %y @1
  ret %r, %t @1
}

func @si16(%x: i16, %y: i16) -> i16, i16 {
^entry:
  %r: i16 = sdiv %x, %y @2
  %t: i16 = srem %x, %y @2
  ret %r, %t @2
}

func @si8(%x: i8, %y: i8) -> i8, i8 {
^entry:
  %r: i8 = sdiv %x, %y @3
  %t: i8 = srem %x, %y @3
  ret %r, %t @3
}

func @ui64(%x: i64, %y: i64) -> i64, i64 {
^entry:
  %r: i64 = udiv %x, %y @4
  %t: i64 = urem %x, %y @4
  ret %r, %t @4
}

func @ui32(%x: i32, %y: i32) -> i32, i32 {
^entry:
  %r: i32 = udiv %x, %y @5
  %t: i32 = urem %x, %y @5
  ret %r, %t @5
}

func @ui16(%x: i16, %y: i16) -> i16, i16 {
^entry:
  %r: i16 = udiv %x, %y @6
  %t: i16 = urem %x, %y @6
  ret %r, %t @6
}

func @ui8(%x: i8, %y: i8) -> i8, i8 {
^entry:
  %r: i8 = udiv %x, %y @7
  %t: i8 = urem %x, %y @7
  ret %r, %t @7
}

locs {
  @0 = "llvm/test/CodeGen/X86/divrem.ll":5:1 to 54:2
  @1 = "llvm/test/CodeGen/X86/divrem.ll":56:1 to 84:2
  @2 = "llvm/test/CodeGen/X86/divrem.ll":86:1 to 115:2
  @3 = "llvm/test/CodeGen/X86/divrem.ll":117:1 to 144:2
  @4 = "llvm/test/CodeGen/X86/divrem.ll":146:1 to 195:2
  @5 = "llvm/test/CodeGen/X86/divrem.ll":197:1 to 225:2
  @6 = "llvm/test/CodeGen/X86/divrem.ll":227:1 to 256:2
  @7 = "llvm/test/CodeGen/X86/divrem.ll":258:1 to 285:2
}
