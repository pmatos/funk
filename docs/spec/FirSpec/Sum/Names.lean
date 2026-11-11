import VersoManual
import Fir.Sum.Names
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on words and dialect sets, which renders
`Fir.Sum.Names` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Words and dialect sets: readable blocks" =>

:::moduleDocs (fingerprint := "17666849479822341420")
:::

:::readable Fir.wordDialect Fir.wordDialect_dot (fingerprint := "1656636787730505960")
*Definition: the dialect that a word names.* $`\mathrm{dialect}(w)` is the
part of the word $`w` before its first $`.`, and is undefined, written
$`\bot`, when $`w` holds no $`.`: a bare word, which is the core's.

$$`\mathrm{dialect}(n.w) = n \quad\text{when } n \text{ holds no } .`

So $`\mathrm{dialect}(\texttt{gpu.launch}) = \texttt{gpu}`,
$`\mathrm{dialect}(\texttt{toy.a.b}) = \texttt{toy}`, and a bare word names
no dialect. The theorem states the equation: a dialect's name, a $`.` and
any word make a word of that dialect.
:::

:::readable Fir.Attr.head? Fir.Attr.dialect? Fir.Attr.dialects Fir.Attr.dialectsAll Fir.Attr.dialect?_mem Fir.Attr.mem_dialectsAll (pin := Fir.Attr) (fingerprint := "13295879490704131267")
*Definition: the dialects of a type or an attribute.* The head of an
attribute is its word, or the word that an applied attribute applies; a
number, a string and a symbol have none. A type belongs to the dialect of
its head, $`\mathrm{dialect}(\mathrm{head}(a))`, so $`\texttt{toy.vec(4, i32)}`
is a type of $`\texttt{toy}`.

$`\mathrm{dialects}(a)` lists the dialect of every word of $`a`, at any
depth: of a word, its dialect if it has one; of an applied attribute, the
dialect of its head and then those of its arguments, in order; of a number,
a string or a symbol, none. The two theorems say that the dialect of a type
is among the dialects of its words, and that the dialects of a list of
attributes are those of its members.
:::

:::readable Fir.DialectName Fir.DialectSet (fingerprint := "10330358948186183694")
*Definition: a dialect's name and its dialect set.* A dialect other than
the core has a _name_, the word before the $`.` of each of its own words.
Every dialect has a _dialect set_ $`\mathrm{names}(d)`: the names of the
dialects that its words may name. A bare word is the core's, and every
dialect may write one, so the core's name is in no set.
:::

:::readable Fir.LawfulDialectSet (fingerprint := "9771981345072976832")
*Definition: a dialect whose words stay in its set.* The words of the
dialect $`d` name only dialects of its set when, for every op instance $`p`
and every valid type $`t`:

* $`\mathrm{dialect}(\mathrm{opname}(p))`, if defined, is in $`\mathrm{names}(d)`;
* every dialect of $`\mathrm{dialects}(a)`, for each attribute $`a` of
  $`\mathrm{opattrs}(p)`, is in $`\mathrm{names}(d)`;
* every dialect of $`\mathrm{dialects}(\mathrm{tyattr}(t))` is in
  $`\mathrm{names}(d)`;
* $`\mathrm{dialect}(k)`, if defined, is in $`\mathrm{names}(d)`, for
  every region kind $`k` that $`d` registers;
* $`\mathrm{dialect}(k)`, if defined, is in $`\mathrm{names}(d)`, for
  every kind of item $`k` that $`d` registers.

A sum reads each word with the dialect that the word names, so a word of
another dialect could not be read back. The core's set is empty, and the
section on the core's words shows that its words are bare. A dialect that
registers no region kind, or no kind of item, meets the last two laws by
default.
:::
