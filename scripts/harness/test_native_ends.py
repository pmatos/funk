"""The relation of a native run's globals to fir-ref's end
(docs/decisions/testing-and-harness.md#native-runs-report-memory)."""

import unittest

import tools
from ends import Alloc, End
from native_ends import Global, read_units, refined
from refine import FAILED, INVALID, PASSED, RETURN, Outcome, Returned, refines


def block(alloc, *units, align=1, memory=0):
    return Alloc(memory, alloc, "global", align, len(units), True, units)


def ptr8(alloc, offset=0):
    return tuple(f"frag(0, ptr({alloc}, {offset}), {i})" for i in range(8))


def le(address):
    return address.to_bytes(8, "little")


# fir-ref's end of a function that returns a pointer to its table, global
# 1, which holds a pointer to offset 1 of global 0, which holds 0x07 0x08.
SOURCE = End(memory=(block(1, *ptr8(0, 1), align=8), block(0, "0x07", "0x08")))
VALUES = ("ptr(1, 0)",)
TYPES = ("ptr",)
# The native globals: @msg at 4096, @table at 8192 pointing to @msg + 1.
MSG = Global("@msg", 0, 4096, bytes([7, 8]))
TABLE = Global("@table", 0, 8192, le(4097))
NATIVE = (MSG, TABLE)


def judge(source, values, native, got, types=TYPES):
    return refines(Outcome(RETURN, values, end=source), Returned(got, native), types)


class Relation(unittest.TestCase):
    def test_a_native_end_that_holds_the_same_memory_refines(self):
        self.assertEqual(judge(SOURCE, VALUES, NATIVE, ("8192",)).status, PASSED)
        self.assertIsNone(refined(SOURCE, VALUES, NATIVE, ("8192",), TYPES))

    def test_a_planted_wrong_store_fails(self):
        wrong = (Global("@msg", 0, 4096, bytes([9, 8])), TABLE)
        j = judge(SOURCE, VALUES, wrong, ("8192",))
        self.assertEqual(j.status, FAILED)
        self.assertIn("unit 0 of allocation 0 of memory 0 is 0x09", j.why)
        self.assertIn("@msg, not 0x07", j.why)

    def test_a_stored_pointer_into_another_global_fails(self):
        other = Global("@other", 0, 12288, bytes([7, 8]))
        wrong = (MSG, Global("@table", 0, 8192, le(12290)), other)
        j = judge(SOURCE, VALUES, wrong, ("8192",))
        self.assertEqual(j.status, FAILED)
        self.assertIn("unit 0 of allocation 1 of memory 0 points into", j.why)

    def test_a_returned_address_at_another_offset_fails(self):
        j = judge(SOURCE, VALUES, NATIVE, ("8193",))
        self.assertEqual(j.status, FAILED)
        self.assertIn("value 1 points into allocation 1", j.why)

    def test_a_pointer_one_past_the_end_is_related_by_its_offset(self):
        # The address one past @msg's two units is where @next starts; the
        # offset that fir-ref gives picks @msg.
        source = End(memory=(block(0, "0x07", "0x08"),))
        native = (MSG, Global("@next", 0, 4098, bytes([1, 2])))
        self.assertIsNone(refined(source, ("ptr(0, 2)",), native, ("4098",), TYPES))

    def test_a_misaligned_global_fails(self):
        native = (MSG, Global("@table", 0, 8196, le(4097)))
        why, invalid = refined(SOURCE, VALUES, native, ("8196",), TYPES)
        self.assertFalse(invalid)
        self.assertIn("has align 8, and the target's global @table is at 8196", why)

    def test_a_global_of_another_size_fails(self):
        native = (Global("@msg", 0, 4096, bytes([7, 8, 0])), TABLE)
        why, _ = refined(SOURCE, VALUES, native, ("8192",), TYPES)
        self.assertIn("has size 2, and the target's 3", why)

    def test_a_global_of_another_memory_is_not_related(self):
        native = (MSG, Global("@table", 1, 8192, le(4097)))
        why, _ = refined(SOURCE, VALUES, native, ("8192",), TYPES)
        self.assertIn("value 1 points into allocation 1", why)

    def test_the_renaming_stays_one_to_one(self):
        # Two allocations of fir-ref's, each pointing at itself, are one
        # native global.
        source = End(memory=(block(0, *ptr8(1)), block(1, *ptr8(1))))
        native = (Global("@g", 0, 4096, le(4096)),)
        why, _ = refined(source, ("ptr(0, 0)",), native, ("4096",), TYPES)
        self.assertIn("no one-to-one renaming", why)

    def test_poison_and_dangling_pointers_are_refined_by_anything(self):
        source = End(memory=(block(0, "poison", *ptr8(9)),))
        native = (Global("@g", 0, 4096, bytes(9)),)
        self.assertIsNone(refined(source, ("ptr(0, 0)",), native, ("4096",), TYPES))

    def test_a_part_of_a_pointer_is_checked_once_its_global_is_related(self):
        # Global 0 holds the low byte of a pointer to global 1, then the
        # whole pointer, which relates global 1 after the byte is read.
        source = End(
            memory=(block(0, "frag(0, ptr(1, 0), 0)", *ptr8(1)), block(1, "0x05"))
        )
        b = Global("@b", 0, 8208, b"\x05")
        good = (Global("@a", 0, 4096, bytes([0x10]) + le(8208)), b)
        self.assertIsNone(refined(source, ("ptr(0, 0)",), good, ("4096",), TYPES))
        bad = (Global("@a", 0, 4096, bytes([0x11]) + le(8208)), b)
        why, invalid = refined(source, ("ptr(0, 0)",), bad, ("4096",), TYPES)
        self.assertFalse(invalid)
        self.assertIn("not byte 0 of the address of the target's @b plus 0", why)

    def test_a_part_of_a_pointer_that_nothing_relates_is_invalid(self):
        source = End(memory=(block(0, "frag(0, ptr(1, 0), 0)"), block(1, "0x05")))
        native = (Global("@a", 0, 4096, bytes([0x10])),)
        j = judge(source, ("ptr(0, 0)",), native, ("4096",))
        self.assertEqual(j.status, INVALID)
        self.assertIn("cannot relate to a native global", j.why)

    def test_a_stored_pointer_with_no_provenance_is_invalid(self):
        source = End(memory=(block(0, "frag(0, ptr(none, 8), 0)"),))
        native = (Global("@a", 0, 4096, bytes([8])),)
        j = judge(source, ("ptr(0, 0)",), native, ("4096",))
        self.assertEqual(j.status, INVALID)
        self.assertIn("whose bytes are fir-ref's address", j.why)

    def test_values_alone_judge_an_end_that_observes_nothing(self):
        j = refines(Outcome(RETURN, ("7",)), Returned(("7",), NATIVE), ["i8"])
        self.assertEqual(j.status, PASSED)


class Reading(unittest.TestCase):
    def test_units_are_hexadecimal_bytes_and_runs_of_zeros(self):
        self.assertEqual(read_units("0a00zeros(3)ff"), bytes([10, 0, 0, 0, 0, 255]))
        self.assertEqual(read_units(""), b"")
        for bad in ("0", "0A", "zeros(01)", "zeros()", "0a 0b"):
            self.assertIsNone(read_units(bad), bad)

    def test_a_memory_report_is_read(self):
        out = (
            '{"values":["4096"],"memory":[{"global":"@\\"a b\\"","memory":0,'
            '"address":"4096","units":"07zeros(16)"}]}\n'
        )
        got = tools.native_values(tools.Ran(0, out, ""), memory=True)
        self.assertEqual(got, ("4096",))
        self.assertEqual(
            got.memory, (Global('@"a b"', 0, 4096, bytes([7]) + bytes(16)),)
        )

    def test_a_report_without_its_memory_or_with_more_is_not_read(self):
        for out in (
            '{"values":[]}',
            '{"memory":[],"values":[]}',
            '{"values":[],"memory":[],"more":1}',
            '{"values":[],"memory":[{"global":"@a","memory":0,"address":"1"}]}',
            '{"values":[],"memory":[{"global":"@a","memory":0,"address":1,"units":""}]}',
            '{"values":[],"memory":[{"global":"@a","memory":-1,"address":"1","units":""}]}',
        ):
            got = tools.native_values(tools.Ran(0, out + "\n", ""), memory=True)
            self.assertIsInstance(got, str, out)


if __name__ == "__main__":
    unittest.main()
