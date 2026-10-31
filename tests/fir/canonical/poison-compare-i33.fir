func @eq_left(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp eq %p, %b @0
  ret %r @0
}

func @eq_right(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp eq %b, %p @0
  ret %r @0
}

func @ne_left(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp ne %p, %b @0
  ret %r @0
}

func @ne_right(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp ne %b, %p @0
  ret %r @0
}

func @slt_left(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp slt %p, %b @0
  ret %r @0
}

func @slt_right(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp slt %b, %p @0
  ret %r @0
}

func @sle_left(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp sle %p, %b @0
  ret %r @0
}

func @sle_right(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp sle %b, %p @0
  ret %r @0
}

func @sgt_left(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp sgt %p, %b @0
  ret %r @0
}

func @sgt_right(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp sgt %b, %p @0
  ret %r @0
}

func @sge_left(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp sge %p, %b @0
  ret %r @0
}

func @sge_right(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp sge %b, %p @0
  ret %r @0
}

func @ult_left(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp ult %p, %b @0
  ret %r @0
}

func @ult_right(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp ult %b, %p @0
  ret %r @0
}

func @ule_left(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp ule %p, %b @0
  ret %r @0
}

func @ule_right(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp ule %b, %p @0
  ret %r @0
}

func @ugt_left(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp ugt %p, %b @0
  ret %r @0
}

func @ugt_right(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp ugt %b, %p @0
  ret %r @0
}

func @uge_left(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp uge %p, %b @0
  ret %r @0
}

func @uge_right(%a: i33, %b: i33) -> i1 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i1 = icmp uge %b, %p @0
  ret %r @0
}

func @select_cond(%c: i1, %a: i33, %b: i33) -> i33 {
^entry:
  %one: i1 = const true @0
  %p: i1 = add nsw %c, %one @0
  %r: i33 = select %p, %a, %b @0
  ret %r @0
}

func @select_first(%c: i1, %a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = select %c, %p, %b @0
  ret %r @0
}

func @select_second(%c: i1, %a: i33, %b: i33) -> i33 {
^entry:
  %one: i33 = const 1 @0
  %p: i33 = add nsw %a, %one @0
  %r: i33 = select %c, %b, %p @0
  ret %r @0
}

locs {
  @0 = unknown
}
