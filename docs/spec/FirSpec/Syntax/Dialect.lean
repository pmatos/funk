import VersoManual
import Fir.Syntax.Dialect
import Fir.Core.Values
import Fir.Validation.Rules
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on dialects, which renders
`Fir.Syntax.Dialect` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Dialects: readable blocks" =>

:::readable Fir.HVector (fingerprint := "12162099509990058066")
*Definition: a vector of values of given types.* Let $`a_1 \dots a_n` be a
list of types, and let $`f` give each type $`a` a set of values $`f(a)`. A
_heterogeneous vector_ for $`a_1 \dots a_n` holds one value of $`f(a_i)`
for each $`a_i`, in order: it is an element of

$$`f(a_1) \times \dots \times f(a_n)`

For the empty list it is the empty vector. Otherwise it is a value of
$`f(a_1)` followed by a vector for $`a_2 \dots a_n`. The Lean calls it
`HVector`.

The values of an op's operands, and of its results, travel in one, as in
LeanMLIR, a formalization of MLIR in Lean. Since the list of types is part
of the vector's type, the
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[semantics]
of an op receives exactly one operand
value for each operand type, each of its type: a wrong number or a wrong
type is ruled out before anything runs.
:::

:::readable Fir.Dialect (fingerprint := "7801125833974356758")
*Definition: a dialect.* A dialect $`D` is a pair of sets: its _op
instances_ $`\mathrm{Op}_D` and its _types_ $`\mathrm{Ty}_D`.

An op instance is one op with its attributes and every type it is used at.
In the {ref "The-fir-specification--Abstract-syntax--Core-ops"}[core dialect],
$`\mathsf{add}` at $`\mathsf{i32}` with the $`\mathsf{nsw}` flag is one op
instance, and $`\mathsf{add}` at $`\mathsf{i64}` is another. So the types of
an op instance's operands and results follow from the op instance alone, and
the dialect's signature, below, gives them.

The dialect is why fir can reach any kind of hardware
(ADR-2026-10-29-2016). The terms, validation, execution and the text format
are each written once, for a dialect $`D` that they take as a parameter.
Nothing in fir is a closed list of all ops or all types: the core dialect is
one dialect, and a dialect for a GPU would be another. A dialect does not
say which effects its ops have, such as choosing a value; its semantics asks
for them in the
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[execution chapter].
:::

:::readable Fir.TyDenote (pin := Fir.Core.Ty.toType) (fingerprint := "11240588567006984445")
*Definition: the values of a type.* A dialect $`D` gives each of its types
$`t \in \mathrm{Ty}_D` the set of its values, written
$`\llbracket t \rrbracket`. The Lean calls this map `toType`.

The values of an op's operands and results are drawn from these sets, so
this is where execution gives meaning to types: a run binds each value name
to an element of the set of its type. In the core dialect,
$`\llbracket \mathsf{i}N \rrbracket` holds poison and the $`N`-bit
integers, and $`\llbracket \mathsf{ptr} \rrbracket` is empty
({ref "The-fir-specification--Execution--Core-values"}[core values]).
:::

:::readable Fir.DialectSignature (pin := Fir.Func.OpValid) (fingerprint := "12890725616559564221")
*Definition: the signature of a dialect.* The signature of a dialect $`D`
gives four facts about each op instance $`o \in \mathrm{Op}_D`:

$$`\begin{aligned} \mathrm{sig}_D(o) &\in \mathrm{Ty}_D^* \\ \mathrm{res}_D(o) &\in \mathrm{Ty}_D^* \\ \mathrm{term}_D(o) &\in \{\mathsf{true}, \mathsf{false}\} \\ \mathrm{nsucc}_D(o) &\in \mathbb{N} \end{aligned}`

* $`\mathrm{sig}_D(o)` is the list of the types of its operands, and
  $`\mathrm{res}_D(o)` the list of the types of its results.
* $`\mathrm{term}_D(o)` says whether $`o` is a _terminator_, an op that
  ends a block.
* $`\mathrm{nsucc}_D(o)` is its number of _successors_, the blocks that
  control may go to next. A terminator goes to one of them, or returns from
  the function.

The Lean spells them `sig`, `returnTypes`, `isTerminator` and `succCount`.

Validation reads the signature to check each op in its place
({ref "The-fir-specification--Validation--The-general-rules"}[the general rules]):
its operands and results have the types of $`\mathrm{sig}_D(o)` and
$`\mathrm{res}_D(o)`, it is a terminator exactly when it is the last op of
its block, it has $`\mathrm{nsucc}_D(o)` successors, and an op that is not
a terminator has none, whatever $`\mathrm{nsucc}_D(o)` says. The signature
says nothing of regions or of kinds of effect: they come with the first
dialect that needs them, and neither is decided yet. The
{ref "The-fir-specification--Abstract-syntax--Core-signatures"}[core signatures]
give the core dialect's.
:::
