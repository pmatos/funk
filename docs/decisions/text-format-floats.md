# Current decisions: float constants and float ops in text

This page continues [text-format.md](text-format.md). It says what holds
today for how float constants and float ops are written. It is the record:
when this page and an ADR disagree, the page wins, and the ADR is fixed or
deleted (ADR-2026-11-09-1610).

## Float constants

A float constant is `const` with one float literal, as LLVM writes it
(ADR-2026-11-11-1438). The human ruled on 2026-11-11: "Decimal float, hex
fallback"; the orchestrator recorded it on #229. The agent that built it chose
the details below.

A zero, or a finite value of a format no wider than `f128` in either field
(`2 <= e <= 15`, `1 <= m <= 112`), is the shortest decimal that reads back to
its bits: `%one: f32 = const 1.0`, `0.1`, `-0.0`, `1.5e-7`. Of two shortest,
the nearer wins, then the one with an even last digit. With `d.ddd · 10^E`
its value, digits are laid out plainly when `-4 <= E < 16`, as `1234.5` or
`0.0001`, and otherwise as one digit, `.`, the rest, `e` and `E`, as
`1.5e-7` or `1.0e16`. There is always a digit after `.`, and no other
trailing zero. Every other value, NaNs and infinities among them, and every
value of a format without decimals, is `0x` and its bits in exactly
`ceil((1 + e + m) / 4)` lowercase hexadecimal digits, leading zeros included,
as `0x7fc00000` or `0x6` for the positive infinity of `float<2,1>`
(ADR-2026-11-11-1438).

The lexer reads a float literal as one token, kept as written. A decimal is
an optional `-`, a whole part with no leading zeros, `.`, one or more digits,
and an optional `e` and integer exponent with no leading zeros and never
`-0`. A whole number followed by `.` and a digit, or `0` followed by `x`,
starts a float literal. The generic attribute `Attr.float` holds one, so any
dialect may use float literals (ADR-2026-11-11-1438).

A decimal reads as its exact value rounded to the format, to nearest with
ties to even, by Lean's float model: its `round` when the value is an
integer, its `div` of the digits by a power of ten otherwise, then `pack`. A
negative decimal that rounds to zero reads as `-0`. The reader first rejects
a decimal whose whole part or fraction has more than 64 digits, or whose
exponent is more than 9999 in magnitude, so it never computes a huge power of
ten. Lean's `ofScientific` is not used: it reads every value below a bound as
zero, and at a format such as `float<2,30>` that bound lies above the
smallest subnormal (ADR-2026-11-11-1438).

A literal decodes only when it is the spelling of the bits it reads as, so
`1.00`, `1.0e0`, `0x3f800000` and `1065353216` at `f32` do not decode, nor
does `1.0e39`, which reads as an infinity, nor `0x7fc0000`, which has seven
digits. Each bit pattern has one spelling, and `print(parse(t)) == t` holds by
construction. `fir-ref run` and the corpus spell float arguments and results
the same way; a built executable keeps its bits read as a signed integer,
which the harness converts exactly (`scripts/harness/native_floats.py`).
`scripts/harness/float_text.py` is the reference that the shared cases of
`tests/dialects/float-text.cases` come from (ADR-2026-11-11-1438).

Rejected: the bits read as a signed integer, `const 1065353216`, the first
spelling, which the human's ruling replaced; the shortest decimal of at most
six digits, as LLVM writes `double`, which sends most `f32` and `f128` values
to hexadecimal; decimals at every format, which can need millions of digits;
and hexadecimal for every value, which the human did not rule
(ADR-2026-11-11-1438).

## Float ops

`fcmp` writes its predicate as LLVM does, one of `oeq`, `one`, `olt`, `ole`,
`ogt`, `oge`, `ord`, `ueq`, `une`, `ult`, `ule`, `ugt`, `uge` and `uno`:
`%lt: i1 = fcmp olt %a, %b` (ADR-2026-11-09-1549).

Each float op that rounds, `fadd`, `fsub`, `fmul`, `fdiv`, `sqrt` and `fma`,
has one attribute, `round(rne)`, in the applied form:
`%s: f32 = fadd round(rne) %a, %b`. `sitofp` and `uitofp` round too, from an
integer of any width to a float of any format, and no other pair of types
decodes (#241). `frem`, `fmod`, `fneg` and `fabs` do not
round, since their result is exact, and have none: `%q: f64 = frem %a, %b`.
Any other attribute does not decode, so a missing mode, `round(rtz)`, the bare
word `rne`, two attributes, `fneg round(rne)` and `frem round(rne)` are parse
errors. The op
carries no mode, since M1 has one; a later mode adds a decoding and a field
(ADR-2026-11-09-1549, ADR-2026-11-11-1801). Rejected: decoding every IEEE
mode and letting validation reject all but `rne`, which gives each op a field
that no valid program sets; no attribute, which drops the hook that keeps
today's texts' meaning when another mode comes; and the bare word `rne`,
which says nothing about what it sets.

`bitcast` has no attribute, and its types say which way it goes:
`%b: i32 = bitcast %f` gives the bits of an `f32`, and `%f: f32 = bitcast %b`
the `f32` of an `i32`'s bits. Its integer has the float's width, `1 + e + m`,
and any other pair of types, two floats or two integers among them, does not
decode, as `fadd` on two types does not, so validation has no rule for it.
Rejected: one name for each direction, which the types already tell apart, and
any pair of widths decoding with validation rejecting the wrong ones, as for
`zext`, which gives the spec an op instance that no program may hold.

`fpext` has no attribute, since it never rounds, and `fptrunc` has
`round(rne)`: `%d: f64 = fpext %f` and `%f: f32 = fptrunc round(rne) %d`. Each
takes one float type to another, and any two formats decode; which pair takes
which op is a rule of validation, as the widths of `zext` and `trunc` are
([semantics-floats-conversions.md](semantics-floats-conversions.md#the-conversions)), so `fpext` from
`f64` to `f32`, or from `bf16` to `f16`, parses and does not validate (#241).
Rejected: decoding only the pairs each op takes, as `bitcast` decodes only its
widths. `bitcast`'s op instance fixes its integer's width from its format, but
`fpext` and `fptrunc` carry both formats, so the spec has an instance for every
pair, and one that did not decode would break the law that every op instance
reads back from its spelling.

`fptosi` and `fptoui` have no attribute: they truncate toward zero, which is
what they mean, and do not round (the human's ruling of 2026-11-12 on #354).
`%i: i32 = fptosi %f` takes a float of any format to an integer of any width,
and no other pair of types decodes. `fptosi round(rne)`, `fptoui round(rtz)` and
any other attribute are parse errors, as an attribute that an op does not have
is (#241). Rejected: `round(rtz)` on both, which would spell their one meaning
as a mode and decode a field that no other value can take.

Open question to the human, raised on 2026-11-11 on #229 and not yet ruled:
whether a wrong rounding mode stays a parse error, as built, or is read and
then rejected by the verifier, as #229's text says. Until the human rules,
what is built holds.
