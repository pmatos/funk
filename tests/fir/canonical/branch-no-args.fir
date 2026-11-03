func @jump(%a: i8, %b: i8) -> i8 {
^entry:
  %s: i8 = add %a, %b @0
  br ^last @0
^middle:
  ret %s @0
^last:
  br ^middle @0
}

func @diamond(%c: i1, %a: i64, %b: i64) -> i64 {
^entry:
  %d: i64 = sub %a, %b @0
  cond_br %c, ^then, ^else @0
^then:
  br ^difference @0
^else:
  br ^sum @0
^difference:
  ret %d @0
^sum:
  %e: i64 = add %a, %b @0
  ret %e @0
}

func @chain(%a: i128) -> i128, i1 {
^entry:
  %one: i128 = const 1 @0
  %b: i128 = add %a, %one @0
  br ^two @0
^two:
  %c: i128 = add %b, %b @0
  br ^three @0
^three:
  %z: i128 = const 0 @0
  %neg: i1 = icmp slt %c, %z @0
  ret %c, %neg @0
}

func @none() {
^entry:
  br ^done @0
^done:
  ret @0
}

locs {
  @0 = unknown
}
