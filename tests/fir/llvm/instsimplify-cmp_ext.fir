func @zext_uge_sext(%x: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @0
  %zext: i64 = zext %x @0
  %cmp: i1 = icmp uge %zext, %sext @0
  ret %cmp @0
}

func @zext_ugt_sext(%x: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @1
  %zext: i64 = zext %x @1
  %cmp: i1 = icmp ugt %zext, %sext @1
  ret %cmp @1
}

func @zext_ult_sext(%x: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @2
  %zext: i64 = zext %x @2
  %cmp: i1 = icmp ult %zext, %sext @2
  ret %cmp @2
}

func @zext_ule_sext(%x: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @3
  %zext: i64 = zext %x @3
  %cmp: i1 = icmp ule %zext, %sext @3
  ret %cmp @3
}

func @zext_sge_sext(%x: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @4
  %zext: i64 = zext %x @4
  %cmp: i1 = icmp sge %zext, %sext @4
  ret %cmp @4
}

func @zext_sgt_sext(%x: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @5
  %zext: i64 = zext %x @5
  %cmp: i1 = icmp sgt %zext, %sext @5
  ret %cmp @5
}

func @zext_slt_sext(%x: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @6
  %zext: i64 = zext %x @6
  %cmp: i1 = icmp slt %zext, %sext @6
  ret %cmp @6
}

func @zext_sle_sext(%x: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @7
  %zext: i64 = zext %x @7
  %cmp: i1 = icmp sle %zext, %sext @7
  ret %cmp @7
}

func @sext_uge_zext(%x: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @8
  %zext: i64 = zext %x @8
  %cmp: i1 = icmp uge %sext, %zext @8
  ret %cmp @8
}

func @sext_ugt_zext(%x: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @9
  %zext: i64 = zext %x @9
  %cmp: i1 = icmp ugt %sext, %zext @9
  ret %cmp @9
}

func @sext_ult_zext(%x: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @10
  %zext: i64 = zext %x @10
  %cmp: i1 = icmp ult %sext, %zext @10
  ret %cmp @10
}

func @sext_ule_zext(%x: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @11
  %zext: i64 = zext %x @11
  %cmp: i1 = icmp ule %sext, %zext @11
  ret %cmp @11
}

func @sext_sge_zext(%x: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @12
  %zext: i64 = zext %x @12
  %cmp: i1 = icmp sge %sext, %zext @12
  ret %cmp @12
}

func @sext_sgt_zext(%x: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @13
  %zext: i64 = zext %x @13
  %cmp: i1 = icmp sgt %sext, %zext @13
  ret %cmp @13
}

func @sext_slt_zext(%x: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @14
  %zext: i64 = zext %x @14
  %cmp: i1 = icmp slt %sext, %zext @14
  ret %cmp @14
}

func @sext_sle_zext(%x: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @15
  %zext: i64 = zext %x @15
  %cmp: i1 = icmp sle %sext, %zext @15
  ret %cmp @15
}

func @zext_ugt_sext_different_operand(%x: i32, %y: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @16
  %zext: i64 = zext %y @16
  %cmp: i1 = icmp ugt %zext, %sext @16
  ret %cmp @16
}

func @sext_ult_zext_different_operand(%x: i32, %y: i32) -> i1 {
^entry:
  %sext: i64 = sext %x @17
  %zext: i64 = zext %y @17
  %cmp: i1 = icmp ult %sext, %zext @17
  ret %cmp @17
}

locs {
  @0 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":4:1 to 15:2
  @1 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":17:1 to 25:2
  @2 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":27:1 to 38:2
  @3 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":40:1 to 48:2
  @4 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":50:1 to 58:2
  @5 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":60:1 to 71:2
  @6 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":73:1 to 81:2
  @7 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":83:1 to 94:2
  @8 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":96:1 to 104:2
  @9 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":106:1 to 117:2
  @10 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":119:1 to 127:2
  @11 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":129:1 to 140:2
  @12 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":142:1 to 153:2
  @13 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":155:1 to 163:2
  @14 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":165:1 to 176:2
  @15 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":178:1 to 186:2
  @16 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":208:1 to 219:2
  @17 = "llvm/test/Transforms/InstSimplify/cmp_ext.ll":221:1 to 232:2
}
