import Fir.Text.Print
import Fir.Validation.Rules

/-!
# Round trips

Two properties tie the parser to the printer (P3, ADR-2026-10-29-2014, as
refined by ADR-2026-10-30-0815):

* `parse(print(m)) == m` for every well-formed module `m`;
* `print(parse(t)) == t` for every text `t` printed from a well-formed
  module.

The second follows from the first. A module is well formed when its printed
form says everything it holds: every name, word and attribute can be written
as a token, every number is in range, and every op can be read back from its
name, its attributes and the types of its operands and results. These
conditions are syntactic. A module that is not well formed, such as one
whose op uses a value it never defines, has no text that parses back to it:
the parser rejects its printed form with a located reason, as the grammar
section says.

Validation implies well-formedness: every valid module can be written and
read back, so two different valid modules never print the same text. This
is `ValidIsWellFormed`, an obligation of every dialect. Validation checks
the names, labels, operand types, successors and location references of a
module, and the writability laws of `LawfulDialectText` cover what the
dialect writes, so the obligation holds for every lawful dialect: the
theorem `validIsWellFormed`, below. The parser is `Fir.parse`, in the
sections that follow. #11 proves the first property for it, and the laws
of `LawfulDialectText` for the core dialect, which give `ValidIsWellFormed`
for it.

The conditions look at every block and op of a function, at any depth: the
blocks of the regions of its ops too. A valid function's ops own no region,
so its blocks at any depth are its blocks.
-/

namespace Fir

open Text

variable {d : Dialect}

/-- Every op of a function, at any depth. -/
def Func.allOps (f : Func d) : List (Operation d) := f.allBlocks.flatMap (·.body)

/-- Ops that own no region have no blocks below them. -/
theorem Operation.regionBlocks_eq_nil :
    ∀ {os : List (Operation d)}, (∀ o ∈ os, o.regions = []) → Operation.regionBlocks os = []
  | [], _ => by simp [Operation.regionBlocks]
  | ⟨_, _, _, _, regions, _⟩ :: _, h => by
    have hr : regions = [] := h _ (List.mem_cons_self ..)
    subst hr
    rw [Operation.regionBlocks, Region.allBlocks,
      Operation.regionBlocks_eq_nil fun o ho => h o (List.mem_cons_of_mem _ ho)]
    rfl

/-- When no op of these blocks owns a region, they are all the blocks, at
any depth. -/
theorem Block.allBlocks_eq_self :
    ∀ {bs : List (Block d)}, (∀ b ∈ bs, ∀ o ∈ b.body, o.regions = []) → Block.allBlocks bs = bs
  | [], _ => by simp [Block.allBlocks]
  | ⟨_, _, _⟩ :: _, h => by
    rw [Block.allBlocks, Operation.regionBlocks_eq_nil (h _ (List.mem_cons_self ..)),
      Block.allBlocks_eq_self fun b hb => h b (List.mem_cons_of_mem _ hb)]
    rfl

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
type and decodes back to itself; and each of its ops can be written and read
back. Its symbol can be any string.
-/
structure Func.WellFormed (f : Func d) : Prop where
  namesUnique : (f.defs.map (·.1)).Nodup
  names : ∀ x ∈ f.defs, isName x.1
  labels : ∀ b ∈ f.allBlocks, isName b.label
  types : ∀ t ∈ f.types, (tyAttr t).IsType ∧ decodeTy (tyAttr t) = some t
  ops : ∀ o ∈ f.allOps, f.OpWellFormed o

/-- A module can be written and read back: each of its functions can, and
each number in its location table is in range. -/
structure Module.WellFormed (m : Module d) : Prop where
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
  have hall : f.allBlocks = f.blocks := Block.allBlocks_eq_self fun b hb o ho => by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ho
    exact (hf.ops b hb i o hi).1
  have hdef : ∀ x t, f.typeOf x = some t → isName x := by
    intro x t ht
    unfold Func.typeOf at ht
    cases hp : f.defs.find? (·.1 == x) with
    | none => simp [hp] at ht
    | some p =>
      have hx : (p.1 == x) = true := List.find?_some (p := fun y : Name × d.Ty => y.1 == x) hp
      rw [← beq_iff_eq.mp hx]
      exact hf.names p (List.mem_of_find?_eq_some hp)
  refine ⟨hf.namesUnique, hf.names, hf.labels, fun t ht => ?_, fun o ho => ?_⟩
  · exact ⟨LawfulDialectText.tyAttr_isType t (hf.types t ht),
      LawfulDialectText.decodeTy_encode t (hf.types t ht)⟩
  · simp only [Func.allOps, hall, List.mem_flatMap] at ho
    obtain ⟨b, hb, ho⟩ := ho
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ho
    obtain ⟨-, hops, hres, -, -, -, hsucc, -, -, -, hloc⟩ := hf.ops b hb i o hi
    refine ⟨LawfulDialectText.opName_isWord _, LawfulDialectText.opAttrs_writable _, hops,
      hres, fun s hs => ?_, ?_⟩
    · obtain ⟨-, tgt, htgt, hargs⟩ := hsucc s hs
      refine ⟨?_, fun a ha => ?_⟩
      · have hl : (tgt.label == s.label) = true :=
          List.find?_some (p := fun b : Block d => b.label == s.label) htgt
        rw [← beq_iff_eq.mp hl]
        exact hf.labels tgt (hall ▸ List.mem_of_find?_eq_some htgt)
      · have hm : f.typeOf a ∈ tgt.params.map (some ·.2) := hargs ▸ List.mem_map_of_mem ha
        obtain ⟨p, -, hp⟩ := List.mem_map.mp hm
        exact hdef a p.2 hp.symm
    · obtain ⟨e, he, hloc⟩ := List.mem_map.mp (show o.loc ∈ m.locs.map (·.1) from hloc)
      exact hloc ▸ (hl.2.1 e he).1

/-- Every valid module of a dialect with lawful text is well formed. -/
theorem validIsWellFormed : ValidIsWellFormed (d := d) :=
  fun _ hm => ⟨fun f hf => (hm.funcs f hf).wellFormed hm.locs, hm.locs.2.1⟩

end Fir
