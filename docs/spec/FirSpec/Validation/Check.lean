import VersoManual
import Fir.Validation.Check
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the validation check, which renders
`Fir.Validation.Check` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The validation check: readable blocks" =>

:::moduleDocs (fingerprint := "12883482886528262281")
:::

:::readable Fir.DecidableDialectValidation (fingerprint := "5366593531323839649")
*Definition: a dialect whose own rules can be decided.* A dialect $`d` is
_decidable_ when there is an algorithm that tells, for every type $`t` of
$`d`, whether $`\vdash_d t~\text{valid}`, another that tells, for every
op context $`C` and op instance $`\mathit{op}`, whether
$`C \vdash_d \mathit{op}~\text{valid}`, and a third that tells, for every
function context $`C`, view $`v` and function $`f`, whether
$`C, v \vdash_d f~\text{valid}`, and a fourth that tells, for every view
$`v`, kind $`k`, function context $`C`, function $`f` and region $`r`,
whether $`C, v, f \vdash_d r : k~\text{valid}`. These are the dialect's
{ref "The-fir-specification--Validation--Scope-and-symbols"}[own rules]; the
check runs the four algorithms wherever the rules ask them. A dialect that
registers no region kind decides the fourth by default: no region of a kind
of its own is valid.

A function that breaks its dialect's rule over a whole function has no
place of its own to report, so the check reports the rule at its entry block,
with the location reference of that block's first op.

The check also compares types, so it asks that the dialect's types can be
compared for equality. Then so can its function types: $`t^* \to r^*`
equals $`t'^* \to r'^*` exactly when $`t^* = t'^*` and $`r^* = r'^*`, which
the check of a $`\mathsf{call}` uses.
:::

:::readable Fir.Problem (fingerprint := "15591333563506851913")
*Definition: a problem.* A _problem_ is one broken rule. It has a message,
in words for people, and says where the rule is broken, with each of these
when the rule is about one:

* the symbol of the function;
* the label of the block;
* the index of the op in its block, counting from 0;
* the op's location reference.

A rule about a block has the location reference of its first op, and a rule
about a label that names more than one block has that of the first such
block. Tools compare whether a module has problems, never their words.
:::

:::readable Fir.valueRef Fir.labelRef (pin := Fir.isName) (pin := Fir.isNameChar) (pin := Fir.isWordStart) (pin := Fir.isLetter) (pin := Fir.Text.quote) (fingerprint := "14969068081634259249")
*Definition: how a problem writes a value and a label.* A problem writes
the value $`x` as the text does: `%x` when $`x` is a
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[name],
one or more of the ASCII letters, the digits, `_` and `.`, and otherwise
`%` followed by $`x` in double quotes, escaped as a string of the
{ref "The-fir-specification--Text-format--Tokens"}[text format] is. A label
$`l` is written `^l`, or `^` followed by $`l` quoted, in the same way.

So a message holds no line break and no hidden character, whatever names
the module uses.
:::

:::readable Fir.Lookup Fir.Lookup.Agrees (fingerprint := "7614588065826123833")
*Definition: what the check of a function looks up, and when it agrees with
a context.* The check of a function asks two questions of its module: the
function type of a symbol, $`\mathrm{symtab}(s)`, and whether the location
table has the reference $`r`, $`\mathrm{hasloc}(r)`. A _lookup_ answers
them; a module builds its lookup once, as hash tables, so that every
question takes about constant time.

A lookup _agrees_ with a
{ref "The-fir-specification--Validation--The-general-rules"}[module context]
$`C` when it gives the same symbol table, and has exactly the references of
$`C`:

$$`\mathrm{symtab} = \mathrm{symtab}_C`

$$`\mathrm{hasloc}(r) \iff r \in \mathrm{locs}_C \ \text{ for every } r`

The theorems about the check of a function hold for every lookup that
agrees with the context the rules use.
:::
