"""The comparison of two ends of a return, as `End.SeenUnder` makes it."""

import unittest

import tools
from ends import ADDRESS, NOTHING, Alloc, End, pointer_memory, refined
from refine import FAILED, PASSED, RETURN, Outcome, refines


def block(alloc, *units, memory=0, kind="global", align=1, live=True):
    return Alloc(memory, alloc, kind, align, len(units), live, units if live else ())


def frag(alloc, i, offset=0, memory=0):
    return f"frag({memory}, ptr({alloc}, {offset}), {i})"


def ptr8(alloc, offset=0):
    """The eight fragments of a pointer of memory 0 into `alloc`."""
    return tuple(frag(alloc, i, offset) for i in range(8))


# A source that returns a pointer into a global holding 0x07 and a pointer
# to a second global, which holds poison.
SOURCE = End(memory=(block(3, *ptr8(5)), block(5, "poison")))
VALUES = ("ptr(3, 0)",)
TYPES = ("ptr",)


def target(*memory, escaped=()):
    return End((), escaped, tuple(memory))


class Comparison(unittest.TestCase):
    def test_the_same_end_under_other_ids_refines(self):
        t = target(block(1, *ptr8(0)), block(0, "0x2a"))
        self.assertIsNone(refined(SOURCE, VALUES, t, ("ptr(1, 0)",), TYPES))

    def test_a_planted_wrong_store_is_caught(self):
        s = End(memory=(block(3, "0x07", "0x00"),))
        t = target(block(1, "0x07", "0x01"))
        why = refined(s, VALUES, t, ("ptr(1, 0)",), TYPES)
        self.assertEqual(why, "unit 1 of allocation 3 of memory 0 is 0x01, not 0x00")

    def test_kind_alignment_size_and_liveness_must_agree(self):
        s = End(memory=(block(0, "0x00"),))
        for other in (
            block(0, "0x00", kind="stack"),
            block(0, "0x00", align=2),
            block(0, "0x00", "0x00"),
            block(0, "0x00", live=False),
        ):
            why = refined(s, ("ptr(0, 0)",), target(other), ("ptr(0, 0)",), TYPES)
            self.assertIsNotNone(why)

    def test_a_stored_pointer_must_point_where_the_source_s_does(self):
        t = target(block(1, *ptr8(0, offset=1)), block(0, "0x2a"))
        why = refined(SOURCE, VALUES, t, ("ptr(1, 0)",), TYPES)
        self.assertIn("not a fragment like frag(0, ptr(5, 0), 0)", why)

    def test_the_renaming_is_one_to_one(self):
        # The source's two allocations, each holding a pointer to itself,
        # cannot both be one allocation of the target.
        s = End(memory=(block(0, *ptr8(1)), block(1, *ptr8(1))))
        t = target(block(0, *ptr8(0)))
        why = refined(s, ("ptr(0, 0)",), t, ("ptr(0, 0)",), TYPES)
        self.assertIn("no one-to-one renaming", why)

    def test_a_dangling_pointer_is_poison(self):
        # The source's stack allocation was freed at the return, so its
        # memory lists nothing: any target value refines the pointer, and
        # a dangling pointer stored in memory too.
        self.assertIsNone(refined(NOTHING, ("ptr(0, 0)",), NOTHING, (ADDRESS,), TYPES))
        s = End(memory=(block(0, *ptr8(9)),))
        t = target(block(0, *("0x00",) * 8))
        self.assertIsNone(refined(s, ("ptr(0, 0)",), t, ("ptr(0, 0)",), TYPES))

    def test_poison_in_memory_is_refined_by_anything(self):
        s = End(memory=(block(0, "poison", "0x01"),))
        t = target(block(0, frag(4, 0), "0x01"))
        self.assertIsNone(refined(s, ("ptr(0, 0)",), t, ("ptr(0, 0)",), TYPES))

    def test_the_target_may_reach_more(self):
        s = End(memory=(block(0, "poison"),))
        t = target(block(0, frag(1, 0)), block(1, "0x05"))
        self.assertIsNone(refined(s, ("ptr(0, 0)",), t, ("ptr(0, 0)",), TYPES))

    def test_the_escaped_lists_match_place_by_place(self):
        s = End((), ((0, 2), (0, 1)), (block(2, "0x01"), block(1, "0x02")))
        t = target(block(7, "0x01"), block(8, "0x02"), escaped=((0, 7), (0, 8)))
        self.assertIsNone(refined(s, (), t, (), ()))
        swapped = target(block(7, "0x01"), block(8, "0x02"), escaped=((0, 8), (0, 7)))
        self.assertIn("is 0x02, not 0x01", refined(s, (), swapped, (), ()))
        self.assertIn("lets 2 allocations escape", refined(s, (), NOTHING, (), ()))

    def test_a_trace_or_an_unwalked_memory_is_not_judged(self):
        self.assertIn("1 event and", refined(End(("e",)), (), NOTHING, (), ()))
        self.assertIn(
            "ran out of steps", refined(End(memory=None), (), NOTHING, (), ())
        )

    def test_a_pointer_with_no_provenance_is_refined_by_itself(self):
        want = ("ptr(none, 8)",)
        self.assertIsNone(refined(NOTHING, want, NOTHING, want, TYPES))
        self.assertIn(
            "not ptr(none, 8)", refined(NOTHING, want, NOTHING, (ADDRESS,), TYPES)
        )

    def test_the_memory_of_a_pointer_type(self):
        self.assertEqual(
            [pointer_memory(t) for t in ("ptr", "ptr(3)", "i64")], [0, 3, None]
        )


class NativeEnds(unittest.TestCase):
    """Native code's end shows no event, lets nothing escape and reaches no
    live allocation, so values alone judge it only when fir-ref's end
    observes nothing either."""

    def test_values_alone_judge_an_end_that_observes_nothing(self):
        ref = Outcome(RETURN, ("7",))
        self.assertEqual(refines(ref, ("7",), ["i8"]).status, PASSED)

    def test_live_memory_that_native_code_does_not_report_fails(self):
        ref = Outcome(RETURN, VALUES, end=SOURCE)
        j = refines(ref, ("4096",), TYPES)
        self.assertEqual(j.status, FAILED)
        self.assertIn("an observer reaches, and the target's is an address", j.why)

    def test_a_poison_or_dangling_pointer_is_refined_by_an_address(self):
        for want in ("poison", "ptr(0, 0)"):
            j = refines(Outcome(RETURN, (want,)), ("4096",), TYPES)
            self.assertEqual(j.status, PASSED)
        j = refines(Outcome(RETURN, ("poison",)), ("x",), TYPES)
        self.assertEqual((j.status, j.why), (FAILED, "value 1, x, is not an address"))

    def test_an_escape_fails(self):
        ref = Outcome(RETURN, (), end=End((), ((0, 0),), (block(0, "0x00"),)))
        self.assertEqual(refines(ref, (), []).status, FAILED)


class Reading(unittest.TestCase):
    def test_fir_ref_s_end_is_read(self):
        ran = tools.Ran(
            0,
            '{"kind":"return","values":["ptr(1, 0)"],"trace":[],'
            '"escaped":[{"memory":0,"alloc":1}],"memory":['
            '{"memory":0,"alloc":1,"kind":"global","align":8,"size":1,'
            '"live":true,"units":["0x07"]},'
            '{"memory":0,"alloc":2,"kind":"heap","align":1,"size":4,"live":false},'
            '{"memory":0,"alloc":5,"kind":null}],"choices":0}\n',
            "",
        )
        end = tools.path(ran, world=True).outcome.end
        self.assertEqual(end.escaped, ((0, 1),))
        self.assertEqual(
            end.memory,
            (
                Alloc(0, 1, "global", 8, 1, True, ("0x07",)),
                Alloc(0, 2, "heap", 1, 4, False, ()),
                Alloc(0, 5, None),
            ),
        )

    def test_a_malformed_end_is_no_report(self):
        short = (
            '{"memory":0,"alloc":1,"kind":"stack","align":1,"size":2,'
            '"live":true,"units":["0x00"]}'
        )
        for end in (
            '"escaped":[],"memory":[]',
            '"trace":[],"memory":[]',
            '"trace":[],"escaped":[{"memory":0}],"memory":[]',
            '"trace":[],"escaped":[],"memory":[{"memory":0,"alloc":1}]',
            '"trace":[],"escaped":[],"memory":[' + short + "]",
        ):
            out = '{"kind":"return","values":[],' + end + ',"choices":0}'
            ran = tools.Ran(0, out, "")
            self.assertIsInstance(tools.path(ran, world=True), str, end)

    def test_an_unwalked_memory_reads_as_none(self):
        out = '{"kind":"return","values":[],"trace":[],"escaped":[],"memory":null,"choices":0}'
        self.assertIsNone(
            tools.path(tools.Ran(0, out, ""), world=True).outcome.end.memory
        )


if __name__ == "__main__":
    unittest.main()
