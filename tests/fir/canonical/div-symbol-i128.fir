func @__funk_rt_udivmod128(%a: i128, %b: i128) -> i128 {
^entry:
  %q: i128 = udiv %a, %b @0
  %k: i128 = const 1 @0
  %r: i128 = sub %q, %k @0
  ret %r @0
}

func @__funk_rt_udiv128(%a: i128, %b: i128) -> i128 {
^entry:
  %q: i128 = udiv %a, %b @0
  %k: i128 = const 2 @0
  %r: i128 = add %q, %k @0
  ret %r @0
}

func @__funk_rt_urem128(%a: i128, %b: i128) -> i128 {
^entry:
  %q: i128 = urem %a, %b @0
  %k: i128 = const 3 @0
  %r: i128 = add %q, %k @0
  ret %r @0
}

func @__funk_rt_sdiv128(%a: i128, %b: i128) -> i128 {
^entry:
  %q: i128 = sdiv %a, %b @0
  %k: i128 = const 4 @0
  %r: i128 = add %q, %k @0
  ret %r @0
}

func @__funk_rt_srem128(%a: i128, %b: i128) -> i128 {
^entry:
  %q: i128 = srem %a, %b @0
  %k: i128 = const 5 @0
  %r: i128 = add %q, %k @0
  ret %r @0
}

func @__funk_rt_magnitudes(%a: i128, %b: i128) -> i128 {
^entry:
  %q: i128 = sdiv %a, %b @0
  %k: i128 = const 6 @0
  %r: i128 = xor %q, %k @0
  ret %r @0
}

func @".Lrt_div128_step"(%a: i128, %b: i128) -> i128 {
^entry:
  %q: i128 = srem %a, %b @0
  %k: i128 = const 7 @0
  %r: i128 = xor %q, %k @0
  ret %r @0
}

func @plain(%a: i128, %b: i128) -> i128, i128, i128, i128 {
^entry:
  %q: i128 = sdiv %a, %b @0
  %r: i128 = srem %a, %b @0
  %u: i128 = udiv %a, %b @0
  %m: i128 = urem %a, %b @0
  ret %q, %r, %u, %m @0
}

func @via(%a: i128, %b: i128) -> i128 {
^entry:
  %x0: i128 = call @__funk_rt_udivmod128 %a, %b @0
  %x1: i128 = call @__funk_rt_udiv128 %a, %b @0
  %x2: i128 = call @__funk_rt_urem128 %a, %b @0
  %x3: i128 = call @__funk_rt_sdiv128 %a, %b @0
  %x4: i128 = call @__funk_rt_srem128 %a, %b @0
  %x5: i128 = call @__funk_rt_magnitudes %a, %b @0
  %x6: i128 = call @".Lrt_div128_step" %a, %b @0
  %s1: i128 = add %x0, %x1 @0
  %s2: i128 = add %s1, %x2 @0
  %s3: i128 = add %s2, %x3 @0
  %s4: i128 = add %s3, %x4 @0
  %s5: i128 = add %s4, %x5 @0
  %s6: i128 = add %s5, %x6 @0
  ret %s6 @0
}

locs {
  @0 = unknown
}
