import VersoManual
import Fir.Text.RoundTrip
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on round trips, which renders
`Fir.Text.RoundTrip` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Round trips: readable blocks" =>

:::moduleDocs (fingerprint := "11232296592506280195")
:::

:::readable Fir.Func.OpWellFormed (pin := Fir.Func.typeOf) (pin := Fir.DialectSignature) (pin := Fir.Location.limit) (fingerprint := "12115051900375411089")
*Definition: an op that can be written and read back.* Let $`f` be a
function and $`o` an op with the op instance $`p`. The op $`o` is _well
formed_ in $`f` when:

* $`\mathrm{opname}(p)` is a word, and every attribute of
  $`\mathrm{opattrs}(p)` can be
  {ref "The-fir-specification--Text-format--Grammar"}[written];
* each operand $`x` of $`o` has a type $`\mathrm{type}_f(x)` in $`f`, and
  these types, in order, are $`\mathrm{sig}(p)`;
* the types of the results of $`o`, in order, are $`\mathrm{ret}(p)`;
* the label of each successor of $`o` is a name, and so is each value that
  the successor passes;
* the location reference of $`o` is below $`2^{32}`.

Here $`\mathrm{type}_f(x)` is the type of the
{ref "The-fir-specification--Validation--Scope-and-symbols"}[first definition]
of $`x` in $`f`, and $`\mathrm{sig}(p)` and $`\mathrm{ret}(p)` are the
operand and result types that the dialect's
{ref "The-fir-specification--Abstract-syntax--Dialects"}[signature] gives
$`p`. The second and third conditions are what the parser needs to read the
op back: it finds the types of the operands where they are defined, and
gives them to the dialect with the op's name and attributes.
:::

:::readable Fir.Func.WellFormed Fir.Item.WellFormed Fir.Item.WellFormedList Fir.Item.wellFormedList_iff Fir.Module.WellFormed Fir.Module.WellFormed.funcs (pin := Fir.Func.defs) (pin := Fir.Func.types) (pin := Fir.LocTable.InLimits) (pin := Fir.Location.numbers) (pin := Fir.Location.limit) (pin := Fir.Module.funcs) (fingerprint := "3091985326477444571")
*Definition: a well-formed function, item and module.* A function
$`f` is _well formed_ when:

* the value names of $`\mathrm{defs}(f)`, every value that $`f` defines,
  are distinct, and each of them is a name;
* the label of each block of $`\mathrm{allblocks}(f)` is a name;
* for each type $`t` of $`\mathrm{types}(f)`, every type that the text of
  $`f` states, $`\mathrm{tyattr}(t)` is written as a type and
  $`\mathrm{decodety}(\mathrm{tyattr}(t)) = t`;
* each op of $`\mathrm{allops}(f)` is well formed in $`f`;
* the body of $`f` is a region of the core's kind, since the text of a
  function names no kind;
* each region of an op of $`\mathrm{allops}(f)` that names a kind names it
  by a word.

Its symbol may be any string, since a symbol that is not a word is quoted.
An item is well formed when it is a well-formed function, or a nested
module whose dialect set names each dialect by a word and each of whose
items is well formed, at any depth. A module is _well formed_ when each
dialect of its set is named by a word, each of its items is well formed,
and its
{ref "The-fir-specification--Abstract-syntax--Locations"}[location table]
is within limits: every reference, line and column in it is below
$`2^{32}`. So each function of a well-formed module is well formed.

These are the conditions under which the printed form of a module says
everything the module holds, so that the parser can give it back. They are
syntactic, and weaker than validity.
:::

:::readable Fir.TextPos Fir.ParseError Fir.Parser (fingerprint := "12275178464376801079")
*Definition: positions, parse errors and parsers.* A position in a text is
a line, counted from 1, and a column, counted in bytes of UTF-8 from 1, as
a {ref "The-fir-specification--Abstract-syntax--Locations"}[location]
counts them. A parse error is a position and a reason. The reason is for
people: tools compare only whether a text is rejected, not why. A parser of
the dialect $`d` takes a text, and gives a module of $`d` or a parse error.
:::

:::readable Fir.PrintThenParse Fir.ParseThenPrint (fingerprint := "13885639623341848841")
*Definition: the two round trips.* Let $`\mathrm{parse}` be a parser, and
$`\mathrm{print}(m)` the
{ref "The-fir-specification--Text-format--The-canonical-printer"}[text]
of the module $`m`. The two round trips are:

* _print then parse_: for every well-formed module $`m`,
  $`\mathrm{parse}(\mathrm{print}(m)) = m`;
* _parse then print_: for every well-formed module $`m_0` and every module
  $`m`, if $`\mathrm{parse}(\mathrm{print}(m_0)) = m` then
  $`\mathrm{print}(m) = \mathrm{print}(m_0)`.

The first says that the text of a well-formed module loses nothing. The
second says that the printer is the formatter: reading a canonical text and
printing it again changes no byte.
:::

:::readable Fir.parseThenPrint_of_printThenParse Fir.print_injective (fingerprint := "5972969231514547260")
*Theorems: the second round trip follows from the first, and different
well-formed modules print differently.* For every dialect with a
signature and a text, and every parser of it for which print then parse
holds:

* parse then print holds too;
* for all well-formed modules $`m_1` and $`m_2`, if
  $`\mathrm{print}(m_1) = \mathrm{print}(m_2)` then $`m_1 = m_2`.

Both are immediate, since the parser gives each text back as the module it
was printed from. The second is worth stating: it is what makes the text a
faithful name for a module, so that tools can compare modules by comparing
their text.
:::

:::readable Fir.ValidIsWellFormed (fingerprint := "3986442221758513856")
*Definition: validation implies well-formedness.* A dialect with its
{ref "The-fir-specification--Validation--Scope-and-symbols"}[validation rules]
meets this obligation when every
{ref "The-fir-specification--Validation--The-general-rules"}[valid module]
of it is well formed. Every dialect owes it: with it, every valid module
can be written and read back, so the round trip covers every valid module,
and two different valid modules never print the same text. The next block
shows that every dialect whose text is lawful meets it.
:::

:::readable Fir.Func.Valid.wellFormed Fir.SymbolTable.Valid.itemsWellFormed Fir.validIsWellFormed (pin := Fir.Func.Valid) (pin := Fir.LocTable.Valid) (pin := Fir.Module.Valid) (pin := Fir.SymbolTable.Valid) (pin := Fir.Location.limit) (fingerprint := "5578296981944101061")
*Theorems: a valid function is well formed, and so is every valid module.*
Let $`d` be a dialect with a signature, a text and validation rules, whose
text is {ref "The-fir-specification--Text-format--Grammar"}[lawful]. Then:

* for every location table that is valid, every function $`f` that is
  {ref "The-fir-specification--Validation--The-general-rules"}[valid] in
  a context whose references are those of the table is well formed;
* the items of a valid symbol table, whose nested tables are all valid,
  are well formed, at any depth;
* every valid module of $`d` is well formed.

The proof reads each condition of well-formedness off a rule of validation
or a law of the text. Every op of a function, at any depth, is an op of
its body or an op inside a region of an op. Validation gives distinct
value names that are names, labels that are names, valid types, a body of
the core's kind, regions of ops whose kinds are words, operand and result
types that match the op instance, successors whose labels are names and
that pass values that the function defines, and location references that
are keys of the table, whose keys are below $`2^{32}`, and dialect sets
whose names are words, the module's own and each nested module's. The
laws give op names that are words, attributes that can be written, and
valid types that are written as types and read back. A nested module is
well formed when its set's names are words and its items are well formed,
which its own table, valid like every table of the module, gives, by
induction on the nesting.
:::
