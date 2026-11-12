"""Tests of how the coverage matrix reads a module's text."""

import unittest

from firtext import Op, TextError, read, tokens

LOOP = """func @sum(%n: i32) -> i32 {
^entry:
  %zero: i32 = const 0 @1
  br ^loop(%zero, %zero) @1
^body:
  %acc1: i32 = add nsw %acc, %i @3
  %one: i32 = const 1 @3
  %i1: i32 = add nsw %i, %one @3
  br ^loop(%i1, %acc1) @3
^loop(%i: i32, %acc: i32):
  %done: i1 = icmp sge %i, %n @2
  cond_br %done, ^exit(%acc), ^body @2
^exit(%r: i32):
  ret %r @4
}

func @"two words"(%a: i8) -> i8, i64 {
^entry:
  %w: i64 = sext %a @0
  %t: i32 = trunc %w @0
  %s: i32 = call @sum %t @0
  %u: i8, %v: i64 = call @"two words" %a @0
  ret %a, %w @0
}

locs {
  @0 = unknown
  @1 = "sum.c":2:3 to 2:14
  @2 = name("x")
  @3 = fused(@1, @2)
  @4 = callsite(@1 at @2)
}
"""


class Tests(unittest.TestCase):
    def test_tokens(self):
        kinds = [
            (t.kind, t.text)
            for t in tokens('%a.1: i8 = const -5 @12 // note\n call @"x y" @f ^b ->')
        ]
        self.assertEqual(
            kinds,
            [
                ("value", "%a.1"),
                (":", ":"),
                ("word", "i8"),
                ("=", "="),
                ("word", "const"),
                ("int", "-5"),
                ("locref", "@12"),
                ("word", "call"),
                ("symbol", '@"x y"'),
                ("symbol", "@f"),
                ("label", "^b"),
                ("->", "->"),
            ],
        )

    def test_a_string_holds_escapes(self):
        self.assertEqual(
            [t.text for t in tokens(r'@"a\"b\\" "c"')], [r'@"a\"b\\"', '"c"']
        )

    def test_functions_and_their_ops(self):
        functions = read(LOOP)
        self.assertEqual(list(functions), ["@sum", '@"two words"'])
        s = functions["@sum"]
        self.assertEqual((s.params, s.results), (("i32",), ("i32",)))
        self.assertEqual(
            s.ops,
            (
                Op("const", ("0",), (), ("i32",), ()),
                Op("br", (), (), (), (("i32", "i32"),)),
                Op("add", ("nsw",), ("i32", "i32"), ("i32",), ()),
                Op("const", ("1",), (), ("i32",), ()),
                Op("add", ("nsw",), ("i32", "i32"), ("i32",), ()),
                Op("br", (), (), (), (("i32", "i32"),)),
                Op("icmp", ("sge",), ("i32", "i32"), ("i1",), ()),
                Op("cond_br", (), ("i1",), (), (("i32",), ())),
                Op("ret", (), ("i32",), (), ()),
            ),
        )
        t = functions['@"two words"']
        self.assertEqual(t.results, ("i8", "i64"))
        self.assertEqual(t.ops[2], Op("call", ("@sum",), ("i32",), ("i32",), ()))
        self.assertEqual(
            t.ops[3], Op("call", ('@"two words"',), ("i8",), ("i8", "i64"), ())
        )
        self.assertEqual(t.callees(), {"@sum", '@"two words"'})
        self.assertEqual(t.ops[4], Op("ret", (), ("i8", "i64"), (), ()))

    def test_a_module_without_functions(self):
        self.assertEqual(read("locs {\n}\n"), {})

    def test_nested_modules_hold_their_own_functions(self):
        text = (
            "dialects toy\n\n"
            "func @g() {\n^e:\n  ret @0\n}\n\n"
            "module @dev() {\n  dialects toy\n\n"
            "  func @g(%a: i8) {\n  ^e:\n    x {\n    } @0\n    ret %b @0\n  }\n\n"
            "  module @inner() {\n  }\n\n}\n\n"
            "func @h() {\n^e:\n  ret @0\n}\n\nlocs {\n  @0 = unknown\n}\n"
        )
        functions = read(text)
        self.assertEqual(list(functions), ["@g", "@h"])
        self.assertEqual(functions["@g"].params, ())

    def test_a_data_layout_is_skipped(self):
        text = (
            "dialects toy\n\n"
            "layout memory(1, unit(8), pointer(32), little), "
            "memory(2, unit(16), pointer(64), big, align(4), nonintegral)\n\n"
            "func @f(%p: ptr(1)) {\n^e:\n  ret @0\n}\n\nlocs {\n  @0 = unknown\n}\n"
        )
        self.assertEqual(read(text)["@f"].params, ("ptr(1)",))

    def test_texts_it_cannot_read(self):
        for text, needle in [
            ("func @f() {\n^e:\n  ret %x @0\n}\nlocs {\n}\n", "%x is not defined"),
            ("global @g() {\n}\nlocs {\n}\n", "an item of kind global"),
            ("module @m() {\n  func @f() {\n", "a nested module does not end"),
            ("layout memory(1, unit(8)", "an entry of the data layout does not end"),
            ("func @f() {\n^e:\n  ret @0\n}\n", "expected word"),
            ("locs {\n}\nfunc", "text after the location table"),
            ('func @"f() {\n', "a string does not end"),
            ("func @f() {\n^e:\n  x {\n  } @0\n}\nlocs {\n}\n", "an op with a region"),
            (
                "func @f(%a: i8) {\n^e:\n  %a: i8 = const 1 @0\n  ret @0\n}\nlocs {\n}\n",
                "defines a value twice",
            ),
            ("func @f() { $ }", "cannot read '$'"),
        ]:
            with self.subTest(text=text):
                with self.assertRaises(TextError) as e:
                    read(text)
                self.assertIn(needle, str(e.exception))


if __name__ == "__main__":
    unittest.main()
