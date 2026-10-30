func @f(%x: i32) -> i32 {
^entry:
  %a: i32 = add %x, %x @2
  %b: i32 = add %a, %x @5
  %c: i32 = add %b, %a @7
  %d: i32 = add %c, %c @9
  %e: i32 = add %d, %c @10
  ret %e @4294967295
}

locs {
  @0 = unknown
  @2 = "f.c":1:1 to 1:1
  @3 = "dir/f\"q\".c":7:0 to 7:0
  @4 = name ( "x\tplus x" )
  @5 = callsite ( @2 at @3 )
  @7 = fused(@2,@3,@4)
  @9 = derived( @7 )
  @10 = "f.c":4294967295:4294967295 to 4294967295:4294967295
  @4294967295 = "":1:9 to 3:2 // the largest reference
}
