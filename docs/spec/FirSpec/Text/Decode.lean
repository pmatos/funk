import VersoManual
import Fir.Text.Decode
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on decoding, which renders
`Fir.Text.Decode` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Decoding: readable blocks" =>

:::moduleDocs (fingerprint := "15291453173045403699")
:::

:::readable Fir.Text.Scope Fir.Text.decodeType Fir.Text.decodeDef Fir.Text.define (pin := Fir.DialectText) (fingerprint := "12263311160479661426")
*Definition: the scope, and adding definitions to it.* The _scope_ of a
function is a table that gives each value the function defines its type.
A type written at the position $`p` is decoded with the dialect's
$`\mathrm{decodety}`, from the
{ref "The-fir-specification--Text-format--Grammar"}[grammar section]; when
it is undefined, the type is an error at $`p`, "does not decode". A
definition decodes to its value's name and its decoded type. Definitions
are added to the scope one by one, in order, and a value that is already
in the scope is an error at its second definition, "is defined twice".
:::

:::readable Fir.Text.defineBlocks Fir.Text.defineOps Fir.Text.defineRegions (fingerprint := "15680766533129011072")
*Definition: the first pass.* The first pass adds every definition of some
blocks to the scope, at any depth, in the order of the text: for each
block, its arguments, then, for each of its ops, the op's results and then
the definitions of the blocks of its regions.
:::

:::readable Fir.Text.operandTypes (fingerprint := "12921155979828935619")
*Definition: the types of an op's operands.* The type of each operand is
the type that the scope gives its value. An operand whose value the
function $`f` does not define is an error at the operand, "value `%x` is
not defined in" $`f`.
:::

:::readable Fir.Text.decodeBlocks Fir.Text.decodeOps Fir.Text.decodeRegions (pin := Fir.DialectText) (fingerprint := "11624169546905247397")
*Definition: the second pass.* The second pass decodes the blocks of a
function, in its scope. A block keeps its label, and decodes its arguments
and then its ops. Each op is decoded in this order:

* the types of its operands, from the scope;
* its results, each with its decoded type;
* its op instance, $`\mathrm{decodeop}(n, a^*, t^*, r^*)`, from its name
  $`n`, its attributes $`a^*`, the types $`t^*` of its operands and the
  types $`r^*` of its results; when it is undefined, the op is an error at
  its name, "does not decode";
* its regions, in turn: each keeps the kind it names, if any, and decodes
  its blocks.

The op keeps its results, its operands by name, its successors as written
and its location reference.
:::

:::readable Fir.Text.decodeFunc (fingerprint := "13471885149451493050")
*Definition: decoding a function.* A function is decoded from its symbol,
its parameters, its result types and its blocks: first its result types,
then the scope, built by the first pass from its parameters and then its
blocks, then its parameters, and then its blocks by the second pass, in
that scope. So its errors are found in that order. Its body is a region of
the core's kind.
:::

:::readable Fir.Text.decodeFuncItem Fir.Text.moduleHeader Fir.Text.decodeDialectItem Fir.Text.decodeItem Fir.Text.decodeGlobal Fir.Text.decodeItems Fir.Text.decodeItems_eq_mapM Fir.Text.decodeMemLayout Fir.Text.decodeModule (fingerprint := "2102019124917897587")
*Definition: decoding an item and a module.* An item decodes as a function,
as a nested module (ADR-2026-11-10-1510), as an aggregate's layout
(ADR-2026-11-16-1546), as a global (ADR-2026-11-09-1546) or as an item of
a dialect's kind
(ADR-2026-11-09-1543):

* a `func` with attributes is an error at its first attribute;
* a `func` whose body holds a dialect set is an error at its kind, "a
  func's body holds blocks, not a dialect set", and one whose body holds
  items is an error at the kind of the first of them;
* any other `func` decodes as a function, without blocks when its body is
  empty;
* a `module` with parameters, results or attributes is an error at the
  first of them;
* a `module` whose body holds blocks is an error at its kind, and one whose
  body is empty decodes as a module with no dialect set and no items;
* any other `module` decodes its items, in order, and keeps its dialect
  set;
* an `aggregate` decodes as its layout, as above;
* a `global` item with parameters or results is an error at the first of
  them, and one whose body is not empty an error at its kind; otherwise it
  decodes as the global its attributes read, as the section on globals
  says, or is an error at the attribute that does not read, or at its kind
  when there are too few;
* an item whose kind is a word of a dialect, a word with a `.`, is an
  error at its kind, "an item of a dialect's kind has an empty body", when
  its body is not empty; otherwise it decodes its result types and its
  parameters, and keeps its kind, its symbol and its attributes as they
  were read, whichever dialects the reader holds;
* an item of any other kind is an error at its kind, "unknown item kind".

A list of items decodes each item in order, and stops at the first error.
A module decodes each entry of its data layout, in order, then its items,
and keeps its dialect set and its location table as they were read. An
entry that
{ref "The-fir-specification--Text-format--Grammar"}[does not decode] is an
error at its position, "not an entry of the data layout". Decoding rejects no dialect set: whether a set
names known dialects, and whether the module's words keep to it, is a rule
of validation, and so is whether a dialect registers the kind of an item.
:::

:::readable Fir.Text.decodeField Fir.Text.decodeAggregate (pin := Fir.Field.decode) (pin := Fir.Aggregate.decodeNumber) (fingerprint := "2851346155990452494")
*Definitions: decoding an aggregate's layout.* A field decodes as
$`\mathrm{decode}` of its attribute says, or is an error at the attribute.
An item of kind `aggregate` decodes when it has no parameters, no results,
an empty body and at least three attributes: `memory(n)`, `size(z)` and
`align(a)`, then its fields, each decoded in turn
(ADR-2026-11-16-1546). It is an error at its first parameter or result, at
its kind when its body is not empty or it has fewer than three attributes,
at the first of the three that does not decode, and at the first field that
does not.
:::

:::readable Fir.parse (pin := Fir.Text.lex) (pin := Fir.Text.readModule) (fingerprint := "11087151413922587211")
*Definition: the parser.* The parser of a dialect with a
{ref "The-fir-specification--Text-format--Grammar"}[text] reads a text in
three steps, and stops at the first error, with its position: it
{ref "The-fir-specification--Text-format--The-parser"}[lexes] the text into
tokens, reads them by the grammar into a module as written, and decodes
that module. It gives the decoded module, or the error.
:::
