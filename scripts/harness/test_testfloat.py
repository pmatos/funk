"""Tests of the TestFloat check's parts that need no TestFloat (#229):
reading `testfloat_gen`'s lines, the `bf16` vectors derived from `f32`'s,
the module that runs a batch, and the judgement of each value."""

import math
import random
import unittest

import float_ref as ref
import testfloat_cases as tc

F32 = ref.Format(8, 23)
BF16 = ref.Format(*tc.BF16)

# A line of `testfloat_gen f32_mulAdd` and the same vector under `-rodd`.
# Its operands are `bf16` values, and rounding the first result to `bf16`
# again gives the wrong answer: the exact result lies just below a tie, and
# rounding to nearest at `f32` lands on the tie.
FMA_NEAREST = "EE8E0000 3CA00000 40800000 EBB18000 01"
FMA_ODD = "EE8E0000 3CA00000 40800000 EBB17FFF 01"


class ParseTest(unittest.TestCase):
    def test_arithmetic_and_comparison(self):
        self.assertEqual(
            tc.parse("add", "87FF E850 E850 01"), tc.Vector((0x87FF, 0xE850), 0xE850)
        )
        self.assertEqual(tc.parse("sqrt", "E850 FE00 10"), tc.Vector((0xE850,), 0xFE00))
        self.assertEqual(tc.parse("lt", "0000 857F 0 00"), tc.Vector((0, 0x857F), 0))

    def test_rejects_wrong_field_count(self):
        with self.assertRaises(ValueError):
            tc.parse("mulAdd", "87FF E850 E850 01")


class Bf16Test(unittest.TestCase):
    def test_rounding_matches_the_reference(self):
        rng = random.Random(229)
        edges = [0, 0x8000, 0x7F7FFFFF, 0x7F7F8000, 0x7F7F7FFF, 0x00018000, 0x00028000]
        samples = edges + [rng.getrandbits(32) for _ in range(5000)]
        for bits in samples:
            want = ref.convert(F32, BF16, bits)
            got = tc.round_to_bf16(bits)
            if tc.is_nan(8, 23, bits):
                self.assertTrue(tc.is_nan(8, 7, got), hex(bits))
            else:
                self.assertEqual(got, want, hex(bits))

    def test_only_bf16_operands_are_kept(self):
        v = tc.parse("add", "3F800000 3F800001 40000000 01")
        self.assertIsNone(tc.to_bf16("add", v))
        v = tc.parse("lt", "3F800000 40000000 1 00")
        self.assertEqual(tc.to_bf16("lt", v), tc.Vector((0x3F80, 0x4000), 1))

    def test_rounding_to_odd_first_is_exact(self):
        odd = tc.to_bf16("mulAdd", tc.parse("mulAdd", FMA_ODD))
        nearest = tc.parse("mulAdd", FMA_NEAREST)
        assert odd is not None
        want = ref.fma(BF16, *odd.operands)
        self.assertEqual(odd.result, want)
        self.assertNotEqual(tc.round_to_bf16(nearest.result), want)


class ModuleTest(unittest.TestCase):
    def test_arithmetic_module(self):
        v = tc.Vector((0x3C00, 0xBC00, 0x8000), 0x8000)
        text = tc.module("f16", 5, 10, "mulAdd", [v])
        self.assertIn("func @v() -> i16 {", text)
        self.assertIn("%x0_1: i16 = const -17408 @0", text)
        self.assertIn("%r0: f16 = fma round(rne) %a0_0, %a0_1, %a0_2 @0", text)
        self.assertIn("ret %s0 @0", text)

    def test_comparison_module_swaps_and_counts(self):
        vs = [tc.Vector((1, 2), 1), tc.Vector((3, 4), 0)]
        text = tc.module("f32", 8, 23, "le", vs)
        self.assertIn("%oge0: i1 = fcmp oge %a0_1, %a0_0 @0", text)
        self.assertIn("%ugt1: i1 = fcmp ugt %a1_0, %a1_1 @0", text)
        cs = tc.checks("le", vs)
        self.assertEqual(text.count(", i1") + 1, len(cs))
        self.assertEqual([c.expected for c in cs[:4]], [True, False, True, False])


class PassesTest(unittest.TestCase):
    def test_a_nan_passes_on_any_nan(self):
        c = tc.Check(tc.Vector((0x7C00, 0xFC00), 0xFE00), None, 0xFE00)
        self.assertTrue(tc.passes(5, 10, c, "32256"))
        self.assertTrue(tc.passes(5, 10, c, "-1"))
        self.assertFalse(tc.passes(5, 10, c, "31744"))

    def test_other_results_pass_on_their_bits(self):
        c = tc.Check(tc.Vector((0x3C00, 0x3C00), 0x4000), None, 0x4000)
        self.assertTrue(tc.passes(5, 10, c, "16384"))
        self.assertFalse(tc.passes(5, 10, c, "16385"))
        neg = tc.Check(tc.Vector((0xBC00,), 0xBC00), None, 0xBC00)
        self.assertTrue(tc.passes(5, 10, neg, "-17408"))
        self.assertFalse(tc.passes(5, 10, neg, "poison"))

    def test_comparisons(self):
        c = tc.Check(tc.Vector((1, 2), 1), "olt", True)
        self.assertTrue(tc.passes(5, 10, c, "true"))
        self.assertFalse(tc.passes(5, 10, c, "false"))


class StrideTest(unittest.TestCase):
    def test_stride_is_coprime_with_level_one(self):
        self.assertEqual(math.gcd(tc.MULADD_STRIDE, 6133248), 1)


if __name__ == "__main__":
    unittest.main()
