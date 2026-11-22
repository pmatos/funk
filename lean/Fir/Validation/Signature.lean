import Fir.Validation.Scope
import Fir.Syntax.FuncAttrs

/-!
The rule of a function's signature. A parameter or a result carries the
attributes after its type in the text, such as the core's extension markers
`sext` and `zext`, and the parameters may end in `...`
(ADR-2026-11-21-1307). The dialect of each parameter's and result's type
says which attributes it allows (`validSigAttrs`), and no function that fir
defines is variadic: only an external declaration may be
(ADR-2026-11-09-1547), whose signature follows the same rule otherwise.
-/

namespace Fir

variable {d : Dialect} [DialectValidation d]

/--
A function's signature is valid when its parameters do not end in `...`,
since defining a variadic function stays out of M1 (ADR-2026-11-09-1548),
it holds the attributes of its parameters and results in the form the text
reads, and the dialect of each parameter's and result's type allows its
attributes (ADR-2026-11-09-1547).
-/
structure Func.SigValid (f : Func d) : Prop where
  notVariadic : f.variadic = false
  paramAttrs : AttrsTrimmed f.params.length f.paramAttrs
  resultAttrs : AttrsTrimmed f.results.length f.resultAttrs
  params : ∀ x ∈ f.params.zip f.paramAttrsAll, validSigAttrs x.1.2 x.2
  results : ∀ x ∈ f.results.zip f.resultAttrsAll, validSigAttrs x.1 x.2

/--
An external declaration is valid when its parameters have distinct names
that can be written, each type it states is valid, it holds the attributes
of its parameters and results in the form the text reads, and the dialect
of each parameter's and result's type allows its attributes. Its parameters
may end in `...`. Its symbol is one of its table's, which the rule of a
symbol table checks.
-/
structure Extern.Valid (e : Extern d) : Prop where
  names : ∀ x ∈ e.params, isName x.1
  namesUnique : (e.params.map (·.1)).Nodup
  types : ∀ t ∈ e.types, validTy t
  paramAttrs : AttrsTrimmed e.params.length e.paramAttrs
  resultAttrs : AttrsTrimmed e.results.length e.resultAttrs
  params : ∀ x ∈ e.params.zip e.func.paramAttrsAll, validSigAttrs x.1.2 x.2
  results : ∀ x ∈ e.results.zip e.func.resultAttrsAll, validSigAttrs x.1 x.2

end Fir
