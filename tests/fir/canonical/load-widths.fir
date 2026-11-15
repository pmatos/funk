func @widths() -> i7, i33, i128 {
^entry:
  %p: ptr = alloca stack i7 @0
  %q: ptr = alloca stack i33 @0
  %r: ptr = alloca stack i128 @0
  %a: i7 = load nonatomic %p @0
  %b: i33 = load nonatomic %q @0
  %c: i128 = load nonatomic %r @0
  ret %a, %b, %c @0
}

locs {
  @0 = unknown
}
