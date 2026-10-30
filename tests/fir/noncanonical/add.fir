func @add3(%a : i32 ,%b:i32,
           %c: i32) -> i32
{
^entry:
  %ab : i32 = add %a , %b @1
  %abc: i32 = add %ab,%c @2
  ret %abc @2
}
func @double(%x: i64) -> i64 { ^entry: %y: i64 = add %x, %x @3 ret %y @3 }
locs {
  @1 = "add.c" : 1 : 12 to 1 : 17
  @2 = "add.c":1:12
       to 1:21
  @3 = "add.c":2:10 to 2:15 }
