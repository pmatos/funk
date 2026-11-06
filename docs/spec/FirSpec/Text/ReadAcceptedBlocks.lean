import VersoManual
import Fir.Text.ReadAcceptedBlocks
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on accepted ops, blocks and regions,
which renders `Fir.Text.ReadAcceptedBlocks` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "Accepted ops, blocks and regions: readable blocks" =>

:::readable Fir.Text.Attr.allWritable_of_forall (pin := Fir.Attr.AllWritable) (fingerprint := "7430246370871112945")
*Lemma: proof plumbing.* For every list of attributes each of which can
be {ref "The-fir-specification--Text-format--Grammar"}[written], the list
can be written. The condition on a list of attributes is defined element
by element: the first attribute can be written, and so can the rest of
the list. This lemma shows that a list meets it when every attribute in it
can be written, which is what the reader of an op's attributes gives, so
that it fits the condition on an op.
:::

:::readable Fir.Text.readBlocks_writable (pin := Fir.Text.readBlocks) (pin := Fir.Text.readOps) (pin := Fir.Text.readOpWithResults) (pin := Fir.Text.readOpBody) (pin := Fir.Text.readRegions) (pin := Fir.Text.ReadsWritable) (pin := Fir.Text.SOp.Writable) (pin := Fir.Text.SBlock.WritableList) (fingerprint := "17238551784082129617")
*Theorem: blocks as read can be written, at any depth.* For every list
of tokens $`\mathit{ts}`, the
{ref "The-fir-specification--Text-format--Reading-the-grammar"}[reader of blocks]
{ref "The-fir-specification--Text-format--What-the-grammar-accepts"}[gives],
on $`\mathit{ts}`, that the blocks it reads can be written: when
$`\mathit{ts}` can be written and the reader reads blocks from it, each
block's label is a name, its arguments can be written, and its ops can be
written, at any depth, and the tokens it leaves can be written.

The reader of blocks calls the reader of ops, which calls the reader of an
op with results or the reader of the rest of an op, which calls the reader
of regions, which calls the reader of blocks again. The proof shows what
each of the five gives, together, by induction that follows the readers'
own recursion. Each case is one reader on one shape of tokens, and assumes
what the readers it calls give on the tokens left to them:

* a block's label comes from a label token, so it is a name, and its
  arguments from the reader of definitions;
* the ops of a list start with a value, the first result of an op, or a
  word, the name of an op without results;
* an op with results reads its first result, the others, `=`, and then its
  name, a word token;
* the rest of an op gives attributes, successors and a location reference
  that can be written, by the lemmas of the previous section, and regions
  that can be written, by the case of the reader of regions;
* a region's blocks come from the reader of blocks.

No case looks inside a reader that it calls (ADR-2026-11-03-0028,
ADR-2026-11-03-0328).
:::
