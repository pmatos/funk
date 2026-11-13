"""Tests of the corpus of #241's conversions between float formats: the
committed files of `tests/fir/canonical/` hold exactly what
`float_convert_cases.py` writes, and each expected result is what
`float_ref.py` computes; and the reference converts as the host does
between `f16`, `f32` and `f64`."""

import struct
import tomllib
import unittest

import float_convert_cases as cases
import float_ref as ref
from float_arith_cases import nan_bits
from float_convert_cases import CANONICAL, FORMATS
from float_ref import Format
from float_text import decode

# The host's formats, through `struct`: `f16` and `f32` pack a double,
# rounding to nearest even, and every double's value is an `f64`.
HOST = {"f16": ("<e", "<H"), "f32": ("<f", "<I"), "f64": ("<d", "<Q")}


def host_convert(s: str, t: str, b: int) -> int:
    """The bits of `b` of `s` converted to `t` by the host, an infinity of
    its sign when it is too large for `t`."""
    x = struct.unpack(HOST[s][0], struct.pack(HOST[s][1], b))[0]
    try:
        return struct.unpack(HOST[t][1], struct.pack(HOST[t][0], x))[0]
    except OverflowError:
        return Format(*FORMATS[t]).inf(x < 0)


def wrong_expectations(module: str, text: str) -> list[str]:
    """The tests of a committed test file whose expected result is not the
    reference's."""
    s, t = cases.pair(module)
    f, g = Format(*FORMATS[s]), Format(*FORMATS[t])
    wrong = []
    for test in tomllib.loads(text)["tests"]:
        if "expect" not in test:
            continue
        [arg], [want] = test["args"], test["expect"]
        if arg == "poison":
            if want != "poison":
                wrong.append(f"{test}: a poison operand gives poison")
            continue
        got = ref.convert(f, g, decode(f.e, f.m, arg))
        if "choices" in test:
            [c] = test["choices"]
            ok = g.decode(got) == ("nan",) and decode(g.e, g.m, want) == nan_bits(
                g, int(c)
            )
        else:
            ok = decode(g.e, g.m, want) == got
        if not ok:
            wrong.append(str(test))
    return wrong


class Tests(unittest.TestCase):
    def test_the_committed_corpus_is_what_the_generator_writes(self):
        for path, text in cases.files().items():
            with self.subTest(path=path):
                committed = (CANONICAL / path).read_text(encoding="utf-8")
                self.assertEqual(committed, text)

    def test_each_expected_result_is_the_reference_s(self):
        for module in cases.FILES:
            with self.subTest(module=module):
                text = (CANONICAL / f"{module}.toml").read_text(encoding="utf-8")
                self.assertEqual(wrong_expectations(module, text), [])

    def test_a_wrong_expected_result_is_found(self):
        module = "float-fptrunc-f64-f32"
        text = (CANONICAL / f"{module}.toml").read_text(encoding="utf-8")
        old = 'args = ["1.0000000596046448"], expect = ["1.0"]'
        self.assertEqual(text.count(old), 1)
        planted = text.replace(old, old.replace('["1.0"]', '["1.0000001"]'))
        self.assertEqual(len(wrong_expectations(module, planted)), 1)

    def test_every_pair_takes_exactly_one_op(self):
        self.assertEqual(len(cases.FILES), 20)
        ops = [m.split("-")[1] for m in cases.FILES]
        self.assertEqual((ops.count("fpext"), ops.count("fptrunc")), (9, 11))
        self.assertIn("float-fptrunc-bf16-f16", cases.FILES)
        self.assertIn("float-fptrunc-f16-bf16", cases.FILES)
        self.assertIn("float-fpext-f16-f128", cases.FILES)
        native = [m for m in cases.FILES if cases.is_native(m)]
        self.assertEqual(native, ["float-fpext-f32-f64", "float-fptrunc-f64-f32"])

    def test_the_host_converts_each_case_as_the_reference_does(self):
        """`struct` rounds a double into `f16` and `f32` once, to nearest
        even, so between the host's formats it is a second reference. A
        NaN is any NaN, so only its being a NaN is compared."""
        for s in HOST:
            for t in HOST:
                if s == t:
                    continue
                f, g = Format(*FORMATS[s]), Format(*FORMATS[t])
                for b in cases.values(f, g):
                    with self.subTest(s=s, t=t, b=hex(b)):
                        host = host_convert(s, t, b)
                        want = ref.convert(f, g, b)
                        if g.decode(want) == ("nan",):
                            self.assertEqual(g.decode(host), ("nan",))
                        else:
                            self.assertEqual(host, want)

    def test_the_cases_reach_each_edge(self):
        f64, f32 = Format(11, 52), Format(8, 23)
        got = {ref.convert(f64, f32, b) for b in cases.values(f64, f32)}
        # Overflow to infinity, the largest finite value, underflow to zero
        # of both signs, the smallest subnormal and a tie to even at 1.
        for want in [
            f32.inf(),
            f32.inf(True),
            0x7F7FFFFF,
            0,
            f32.sign_bit,
            1,
            0x3F800000,
        ]:
            self.assertIn(want, got)
        bf16, f16 = Format(8, 7), Format(5, 10)
        down = [ref.convert(bf16, f16, b) for b in cases.values(bf16, f16)]
        self.assertIn(f16.inf(), down)
        self.assertIn(1, down)
        up = [ref.convert(f16, bf16, b) for b in cases.values(f16, bf16)]
        # `1 + 2^-8` is a tie at `bf16` and goes to 1.
        self.assertIn(f16.exact(1 + ref.TWO**-8), cases.values(f16, bf16))
        self.assertIn(bf16.exact(1 + ref.TWO**-6), up)

    def test_every_case_is_tested_once_with_poison(self):
        for module in cases.FILES:
            s, t = cases.pair(module)
            n = len(cases.values(Format(*FORMATS[s]), Format(*FORMATS[t]))) + 1
            text = (CANONICAL / f"{module}.toml").read_text(encoding="utf-8")
            tests = tomllib.loads(text)["tests"]
            with self.subTest(module=module):
                self.assertEqual(len([x for x in tests if "expect" in x]), n)
                plain = [x for x in tests if "expect" not in x]
                self.assertEqual(len(plain), n - 3 if cases.is_native(module) else 0)


if __name__ == "__main__":
    unittest.main()
