import Fir.Text.Print
import Fir.Validation.Rules

/-!
Two properties tie the parser to the printer (ADR-2026-10-29-2014, as
refined by ADR-2026-10-30-0815):

* parsing the text of a well-formed module gives the module back;
* printing what the parser reads from the text of a well-formed module
  gives that text back.

The second follows from the first. A module is well formed when its printed
form says everything it holds: every name, word and attribute can be written
as a token, every number is in range, and every op can be read back from its
name, its attributes and the types of its operands and results. These
conditions are syntactic. A module that is not well formed, such as one
whose op uses a value it never defines, has no text that parses back to it:
the parser rejects its printed form with a located reason, as the grammar
section says.

Validation implies well-formedness: every valid module can be written and
read back, so two different valid modules never print the same text. Every
dialect owes this. Validation checks the names, labels, operand types,
successors and location references of a module, and the laws of a lawful
text cover what the dialect writes, so it holds for every dialect whose
text is lawful: the last theorem of this section. The sections that follow
define the parser, and the section "The round trip, proved", later in this
chapter, proves the first property for it, for every dialect whose text
is lawful. The next section proves that the core dialect's text is lawful,
so every valid core module is well formed.

The conditions look at every block and op of a function, at any depth: the
blocks of the regions of its ops too. Every op of a valid function is an op
of its body or an op inside a region of an op, and validation gives each
what the conditions ask.

This section gives, in order: the ops of a function at any depth; what makes an op, a function and a module
well formed; positions, errors and parsers; the two round trips and how
they relate; and the theorems that valid modules are well formed.
-/

namespace Fir

open Text

variable {d : Dialect}

/-- Every op of a function, at any depth. -/
def Func.allOps (f : Func d) : List (Operation d) := f.allBlocks.flatMap (·.body)

variable [DialectSignature d] [DialectText d]

/-- An op can be written, and read back from its context. -/
def Func.OpWellFormed (f : Func d) (o : Operation d) : Prop :=
  isWord (opName o.op) ∧ Attr.AllWritable (opAttrs o.op) ∧
  o.operands.map f.typeOf = (sig o.op).map some ∧
  o.results.map (·.2) = returnTypes o.op ∧
  (∀ s ∈ o.succs, isName s.label ∧ ∀ a ∈ s.args, isName a) ∧
  o.loc < Location.limit

/--
A function can be written and read back: its value names are unique and can
be written; its labels can be written; each type it states is written as a
type and decodes back to itself; each of its ops can be written and read
back; its body is a region of the core's kind, which the text of a function
does not name; and each region of its ops that names a kind names it by a
word. Its symbol can be any string.
-/
structure Func.WellFormed (f : Func d) : Prop where
  namesUnique : (f.defs.map (·.1)).Nodup
  names : ∀ x ∈ f.defs, isName x.1
  labels : ∀ b ∈ f.allBlocks, isName b.label
  types : ∀ t ∈ f.types, (tyAttr t).IsType ∧ decodeTy (tyAttr t) = some t
  ops : ∀ o ∈ f.allOps, f.OpWellFormed o
  bodyKind : f.body.kind = none
  kinds : ∀ o ∈ f.allOps, ∀ r ∈ o.regions, ∀ k ∈ r.kind, isWord k

/-- A module can be written and read back: each dialect of its set is named
by a word, each of its functions can be written and read back, and each
number in its location table is in range. -/
structure Module.WellFormed (m : Module d) : Prop where
  dialects : ∀ x ∈ m.dialects, isWord x
  funcs : ∀ f ∈ m.funcs, f.WellFormed
  locs : m.locs.InLimits

/-- A position in a text: a line and a column, counted as in locations.
Lines count from 1, and columns count UTF-8 bytes from 1. -/
structure TextPos where
  line : Nat
  col : Nat
  deriving Repr, DecidableEq

/-- Why a parser rejects a text, and where. The reason is for people; tools
compare only whether a text is rejected. -/
structure ParseError where
  pos : TextPos
  reason : String
  deriving Repr

/-- A parser: from text to a module, or to a located error. -/
abbrev Parser (d : Dialect) := String → Except ParseError (Module d)

/-- `parse(print(m)) == m` for every well-formed module. -/
def PrintThenParse (parse : Parser d) : Prop :=
  ∀ m : Module d, m.WellFormed → parse m.print = .ok m

/-- `print(parse(t)) == t` for every text printed from a well-formed module. -/
def ParseThenPrint (parse : Parser d) : Prop :=
  ∀ m₀ : Module d, m₀.WellFormed → ∀ m, parse m₀.print = .ok m → m.print = m₀.print

/-- The second round trip follows from the first. -/
theorem parseThenPrint_of_printThenParse {parse : Parser d}
    (h : PrintThenParse parse) : ParseThenPrint parse := by
  intro m₀ hw m hp
  rw [h m₀ hw] at hp
  cases hp
  rfl

/-- With the first round trip, two different well-formed modules never print
the same text. -/
theorem print_injective {parse : Parser d} (h : PrintThenParse parse)
    {m₁ m₂ : Module d} (h₁ : m₁.WellFormed) (h₂ : m₂.WellFormed)
    (he : m₁.print = m₂.print) : m₁ = m₂ := by
  have e₁ := h m₁ h₁
  rw [he, h m₂ h₂] at e₁
  cases e₁
  rfl

/-- Every valid module of the dialect is well formed: an obligation of every
dialect, which the writability laws of `LawfulDialectText` make hold
(`validIsWellFormed`). -/
def ValidIsWellFormed [DialectValidation d] : Prop :=
  ∀ m : Module d, m.Valid → m.WellFormed

variable [DialectValidation d] [LawfulDialectText d]

/-- A function valid in a module whose location table is valid is well
formed. -/
theorem Func.Valid.wellFormed {m : Module d} {f : Func d} (hf : f.Valid m.context)
    (hl : LocTable.Valid m.locs) : f.WellFormed := by
  have hdef : ∀ x t, f.typeOf x = some t → isName x := by
    intro x t ht
    unfold Func.typeOf at ht
    cases hp : f.defs.find? (·.1 == x) with
    | none => simp [hp] at ht
    | some p =>
      have hx : (p.1 == x) = true := List.find?_some (p := fun y : Name × d.Ty => y.1 == x) hp
      rw [← beq_iff_eq.mp hx]
      exact hf.names p (List.mem_of_find?_eq_some hp)
  have hgen : ∀ o ∈ f.allOps, f.RegionsValid m.context o ∧
      o.operands.map f.typeOf = (sig o.op).map some ∧ o.results.map (·.2) = returnTypes o.op ∧
      (∀ s ∈ o.succs, isName s.label ∧ ∀ a ∈ s.args, isName a) ∧ o.loc ∈ m.context.locKeys := by
    intro o ho
    simp only [Func.allOps, List.mem_flatMap] at ho
    obtain ⟨b, hb, ho⟩ := ho
    rcases Func.mem_allBlocks_cases hb with hb | ⟨b₀, hb₀, o₀, ho₀, r, hr, hbr⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ho
      obtain ⟨hreg, hops, hres, -, -, -, hsucc, -, -, -, hloc⟩ := hf.ops b hb i o hi
      refine ⟨hreg, hops, hres, fun s hs => ?_, hloc⟩
      obtain ⟨-, tgt, htgt, hargs⟩ := hsucc s hs
      refine ⟨?_, fun a ha => ?_⟩
      · have hl : (tgt.label == s.label) = true :=
          List.find?_some (p := fun b : Block d => b.label == s.label) htgt
        rw [← beq_iff_eq.mp hl]
        exact hf.labels tgt (Block.mem_allBlocks (List.mem_of_find?_eq_some htgt))
      · have hm : f.typeOf a ∈ tgt.params.map (some ·.2) := hargs ▸ List.mem_map_of_mem ha
        obtain ⟨p, -, hp⟩ := List.mem_map.mp hm
        exact hdef a p.2 hp.symm
    · have hin : o ∈ o₀.innerOps := by
        simp only [Operation.innerOps, List.mem_flatMap]
        exact ⟨r, hr, b, hbr, ho⟩
      obtain ⟨hreg, hops, hres, -, -, hsucc, -, -, hloc⟩ := hf.inner b₀ hb₀ o₀ ho₀ o hin
      refine ⟨hreg, hops, hres, fun s hs => ⟨(hsucc s hs).1, fun a ha => ?_⟩, hloc⟩
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp ((hsucc s hs).2 a ha)
      exact hdef a t ht
  refine ⟨hf.namesUnique, hf.names, hf.labels, fun t ht => ?_, fun o ho => ?_, hf.bodyKind,
    fun o ho r hr k hk => ?_⟩
  · exact ⟨LawfulDialectText.tyAttr_isType t (hf.types t ht),
      LawfulDialectText.decodeTy_encode t (hf.types t ht)⟩
  · obtain ⟨-, hops, hres, hsucc, hloc⟩ := hgen o ho
    refine ⟨LawfulDialectText.opName_isWord _, LawfulDialectText.opAttrs_writable _, hops,
      hres, hsucc, ?_⟩
    obtain ⟨e, he, hloc⟩ := List.mem_map.mp (show o.loc ∈ m.locs.map (·.1) from hloc)
    exact hloc ▸ (hl.2.1 e he).1
  · exact ((hgen o ho).1.2 r hr k (Option.mem_def.mp hk)).1

/-- Every valid module of a dialect with lawful text is well formed. -/
theorem validIsWellFormed : ValidIsWellFormed (d := d) :=
  fun _ hm => ⟨hm.dialectNames, fun f hf => (hm.funcs f hf).wellFormed hm.locs, hm.locs.2.1⟩

end Fir
