import VersoManual
import Fir.Syntax.Global
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on globals, which renders
`Fir.Syntax.Global` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Globals: readable blocks" =>

:::moduleDocs (fingerprint := "8681767475507853065")
:::

:::readable Fir.Linkage Fir.InitPiece Fir.Global (fingerprint := "1697224336894891665")
*Definition: a global.* A global is an item that names a block of units
of one memory, live for the whole run, with its first contents
(ADR-2026-11-09-1546). It holds no fir value and states no type: its
initializer is units and addresses, as an assembler writes data and
relocations.

```grammar Fir.Linkage
\mathit{linkage}
internal \mathsf{internal}
exported \mathsf{exported}
```

```grammar Fir.InitPiece
\mathit{piece}
units \mathsf{units}~u^*
zeros \mathsf{zeros}~n
addr  \mathsf{addr}~s~k
```

```grammar Fir.Global
\mathit{global}
name,mem,size,align,const,linkage,init \begin{array}{l} \{\mathsf{name}~s,~\mathsf{mem}~n, \\ \enspace \mathsf{size}~z,~\mathsf{align}~a, \\ \enspace \mathsf{const}~b,~\mathsf{linkage}~\mathit{linkage}, \\ \enspace \mathsf{init}~\mathit{piece}^*\,\} \end{array}
```

The global $`s` has $`z` units of the memory $`n`, aligned to $`a` units.
Its initializer fills them in order from the first: $`\mathsf{units}~u^*`
gives units one by one, each the number its bits write;
$`\mathsf{zeros}~n` gives $`n` zero units; and $`\mathsf{addr}~s'~k`
gives the address of the global $`s'` plus $`k` units, which takes the
units of one pointer of the memory of $`s'`. When $`b` holds, the global
is constant, and writing it is UB. Its linkage is $`\mathsf{internal}`,
seen by the module alone, or $`\mathsf{exported}`, seen by code that funk
did not compile too.
:::
