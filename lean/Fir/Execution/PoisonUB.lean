/-!
This section explains, in plain words, why fir has two kinds of undefined
behaviour, how they differ, and what `freeze` does. It defines nothing: the
rules it explains are the op rules of the abstract syntax chapter and the
definitions of this chapter, which follow S1 (ADR-2026-10-29-2006) and
ADR-2026-10-30-0818.

# Two kinds of failure

_Immediate UB is an event._ It happens at one moment of a run: when an op
whose rules say "immediate UB" runs, such as a division by zero. From that
moment the run has no meaning at all. A source run that hits immediate UB
allows the target to do anything (S4, ADR-2026-10-29-2008).

_Poison is a value._ Some failures do not stop the run. An `add nsw` that
overflows produces poison, and the run goes on. Poison flows into the ops
that use it and, by default, makes their results poison too. Nothing goes
wrong unless poison reaches a place where a defined value is needed: a
branch condition, or a divisor. Poison is deferred UB: a failure that is
recorded in a value, and that becomes UB only if it is used in such a place.

# Why defer at all

Deferring lets a compiler move ops. Take a function that computes a sum only
when `%ok` holds:

```
^entry:
  cond_br %ok, ^then, ^join @0
^then:
  %s: i32 = add nsw %a, %b @0
  ...
```

A compiler wants to compute `%s` before the branch, to start it early or to
share it with other code. If an overflowing `add nsw` were immediate UB, it
could not: when `%ok` is false, the source never runs the add and has no UB,
but the moved add could overflow and add UB that the source does not have.
Because overflow gives poison, the moved add only computes a poison that
nothing uses when `%ok` is false. Poison is what makes such ops safe to
compute early, or on a path where their result is not needed.

# Can't UB just be poison?

No, for the ops whose failure the hardware cannot defer.

* _Division by zero._ On x86-64, `idiv` and `div` trap when the divisor is
  zero. If dividing by zero gave poison, the compiler could compute a
  division early, as it does an `add nsw`, and move it above the check that
  keeps its divisor away from zero. The native code would then trap where
  the source did not, so a backend would have to guard every division it
  emits. As immediate UB, a division by zero allows the trap, and a
  division is never moved to where its divisor may be zero. The same holds
  for `INT_MIN / -1`, which traps too. A poison divisor is UB for the same
  reason: it might be zero.
* _A branch on poison._ A branch produces no value that could be poison. It
  only chooses which block runs next, and the run must go somewhere. So the
  choice is not between UB and poison: it is between UB and letting the
  branch go either way. The next section says why fir chooses UB.

And poison cannot become UB either: that would undo the deferral above.

# Why a branch on poison is UB, not a free choice

Compilers learn facts from branches. After this branch, in `^same`, `%x`
and `%y` are equal, so a compiler may replace a use of `%y` with `%x`, as
global value numbering does:

```
  %c: i1 = icmp eq %x, %y @0
  cond_br %c, ^same, ^other @0
^same:
  ret %y @0          // rewritten to: ret %x @0
```

Suppose `%x` is poison and `%y` is `7`. Then `%c` is poison. If a branch on
poison could go either way, the source could reach `^same` and return `7`,
while the rewritten target returns poison there. A poison result does not
refine `7`, so the rewrite would be wrong, and a compiler could not use
what it learns from a branch. Because a branch on poison is immediate UB,
every source run that reaches `^same` through a poison `%c` has already hit
UB, which allows anything, and the rewrite is sound. LLVM makes the same
choice, for the same reason.

# What `freeze` does

`freeze` stops poison. `%f = freeze %p` gives `%p` unchanged when it is a
value. When `%p` is poison, it gives some arbitrary value of the type, and
every use of `%f` sees that same value. So `xor %f, %f` is `0`, and
`icmp eq %f, %f` is `true`, although nobody knows which value was chosen.
A frozen value is never poison, so it is safe to branch on or to divide by.

Since `freeze` of poison may give any value, one function run on one input
can end in more than one way. Its behaviour is the set of its outcomes over
all the values `freeze` may choose (ADR-2026-10-29-2017), and the reference
interpreter models `freeze` of poison as a choice.

# `select` and `cond_br`

`select %c, %a, %b` is a value, while `cond_br %c, ^a, ^b` is a jump. So a
poison condition gives poison in a `select`, which can be computed early
like any other value, and immediate UB in a `cond_br`. This asymmetry makes
some rewrites sound in one direction only. Each of the two below is
forbidden, and #16 tests both.

* _A `select` becomes a branch only with its condition frozen._ Turning a
  `cond_br` and its two arms into a `select` is sound: where the source
  branched on poison, it had UB, which allows the target's poison. Turning
  a `select` into a `cond_br` is not: where the source gave poison, the
  target would have UB. It is sound once the condition is frozen first:
  `%f = freeze %c`, then `cond_br %f, ...`.
* _`select %c, %x, false` is not `and %c, %x`_, where both are `i1` and
  `%x` may be poison. When `%c` is `false`, the `select` gives `false`
  whatever `%x` is, because the value not chosen does not matter. The `and`
  gives poison, because a poison operand propagates. So replacing the
  `select` with the `and` is wrong. The other direction is sound, and so is
  `and %c, %g` with `%g = freeze %x`.
-/
