func @widths(%a: i1, %b: i7, %c: i8, %d: i16, %e: i33, %f: i64, %g: i128) -> i1, i7, i8, i16, i33, i64, i128 {
^entry:
  %pa: ptr = alloca stack i1 @0
  %pb: ptr = alloca stack i7 @0
  %pc: ptr = alloca stack i8 @0
  %pd: ptr = alloca stack i16 @0
  %pe: ptr = alloca stack i33 @0
  %pf: ptr = alloca stack i64 @0
  %pg: ptr = alloca stack i128 @0
  store nonatomic %a, %pa @0
  store nonatomic %b, %pb @0
  store nonatomic %c, %pc @0
  store nonatomic %d, %pd @0
  store nonatomic %e, %pe @0
  store nonatomic %f, %pf @0
  store nonatomic %g, %pg @0
  %ra: i1 = load nonatomic %pa @0
  %rb: i7 = load nonatomic %pb @0
  %rc: i8 = load nonatomic %pc @0
  %rd: i16 = load nonatomic %pd @0
  %re: i33 = load nonatomic %pe @0
  %rf: i64 = load nonatomic %pf @0
  %rg: i128 = load nonatomic %pg @0
  ret %ra, %rb, %rc, %rd, %re, %rf, %rg @0
}

func @padding_wide(%v: i20) -> i24 {
^entry:
  %p: ptr = alloca stack i32 @0
  store nonatomic %v, %p @0
  %w: i24 = load nonatomic %p @0
  ret %w @0
}

locs {
  @0 = unknown
}
