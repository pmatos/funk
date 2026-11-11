"""Tests of the stand-ins that native code gets in place of a poison
argument."""

import unittest

from refine import is_value
from standins import standins, vectors

I8 = ("0", "1", "-1", "-128", "127")


class Standins(unittest.TestCase):
    def test_the_boundary_bit_patterns_of_each_width(self):
        self.assertEqual(standins("i1"), ("false", "true"))
        self.assertEqual(standins("i2"), ("0", "1", "-1", "-2"))
        self.assertEqual(standins("i7"), ("0", "1", "-1", "-64", "63"))
        self.assertEqual(standins("i8"), I8)
        self.assertEqual(
            standins("i64"),
            ("0", "1", "-1", "-9223372036854775808", "9223372036854775807"),
        )
        self.assertEqual(standins("i128")[3], str(-(1 << 127)))
        self.assertEqual(standins("i128")[4], str((1 << 127) - 1))

    def test_each_stand_in_is_a_value_of_its_type(self):
        for w in (1, 2, 3, 7, 8, 16, 32, 33, 64, 128, 1000):
            ty = f"i{w}"
            got = standins(ty)
            self.assertEqual(len(got), len(set(got)), ty)
            self.assertTrue(all(is_value(v, ty) for v in got), ty)

    def test_a_float_type_has_the_boundary_bit_patterns_of_its_bits(self):
        # +0, the smallest subnormal, a NaN with its sign set, -0 and a NaN,
        # each its one float literal (ADR-2026-11-11-1438).
        self.assertEqual(
            standins("f32"), ("0.0", "1.0e-45", "0xffffffff", "-0.0", "0x7fffffff")
        )
        self.assertEqual(standins("f16"), ("0.0", "6.0e-8", "0xffff", "-0.0", "0x7fff"))
        self.assertEqual(standins("float(2, 1)"), ("0.0", "0.5", "0xf", "-0.0", "0x7"))
        self.assertEqual(
            standins("float(16, 3)"),
            ("0x00000", "0x00001", "0xfffff", "0x80000", "0x7ffff"),
        )
        for ty in ("f16", "bf16", "f32", "f64", "f128", "float(5, 2)", "float(16, 3)"):
            got = standins(ty)
            self.assertTrue(all(is_value(v, ty) for v in got), ty)
        self.assertFalse(is_value("true", "f32"))
        self.assertFalse(is_value("-2147483648", "f32"))
        self.assertFalse(is_value("1.00", "f32"))
        self.assertFalse(is_value("0x3f800000", "f32"))
        self.assertTrue(is_value("-0.0", "f32"))

    def test_a_type_with_no_values_has_none(self):
        for ty in ("ptr", "i0", "i08", "f8", "float", "float(5)", ""):
            self.assertIsNone(standins(ty), ty)


class Vectors(unittest.TestCase):
    def test_arguments_with_no_poison_run_as_they_are(self):
        self.assertEqual(vectors(("1", "true"), ["i8", "i1"]), [("1", "true")])
        self.assertEqual(vectors((), []), [()])

    def test_each_poison_takes_each_stand_in_of_its_type(self):
        self.assertEqual(vectors(("poison", "5"), ["i8", "i8"]), [(v, "5") for v in I8])
        self.assertEqual(
            vectors(("true", "poison"), ["i1", "i1"]),
            [("true", "false"), ("true", "true")],
        )

    def test_several_poison_arguments_run_in_every_combination(self):
        got = vectors(("poison", "7", "poison"), ["i1", "i32", "i8"])
        self.assertEqual(len(got), 10)
        self.assertEqual(got[:5], [("false", "7", v) for v in I8])
        self.assertEqual(got[5:], [("true", "7", v) for v in I8])
        self.assertEqual(len(vectors(("poison",) * 3, ["i8"] * 3)), 125)

    def test_why_there_are_none(self):
        self.assertEqual(
            vectors(("poison",), ["ptr"]),
            "argument 1 is poison, and ptr has no stand-in for it",
        )
        self.assertEqual(
            vectors(("poison",), ["i8", "i8"]),
            "the test gives 1 argument for 2 parameters",
        )
        self.assertEqual(vectors(("poison",), None), "cannot read the parameter types")


if __name__ == "__main__":
    unittest.main()
