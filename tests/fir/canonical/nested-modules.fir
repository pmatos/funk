func @main(%a: i32) -> i32 {
^e:
  %r: i32 = call @g %a @0
  ret %r @1
}

func @g(%a: i32) -> i32 {
^e:
  %b: i32 = add %a, %a @2
  ret %b @2
}

module @dev() {
  func @g(%a: i32) -> i32 {
  ^e:
    %b: i32 = call @h %a @3
    ret %b @3
  }

  func @h(%a: i32) -> i32 {
  ^e:
    ret %a @4
  }

  module @main() {
    func @g() {
    ^e:
      ret @4
    }

  }

  module @empty() {
  }

}

locs {
  @0 = "nested-modules.c":3:5 to 3:9
  @1 = "nested-modules.c":4:5 to 4:13
  @2 = unknown
  @3 = derived(@2)
  @4 = unknown
}
