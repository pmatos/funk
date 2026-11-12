import Fir.Text.Print
import Fir.Validation.Rules

/-!
Two properties tie the parser to the printer (ADR-2026-10-29-2014):

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
blocks of the regions of its ops too, and the ops of all those blocks, as
the section on scope and symbols defines them. Every op of a valid
function is an op of its body or an op inside a region of an op, and
validation gives each what the conditions ask.

This section gives, in order: what makes an op, a function and a module
well formed; positions, errors and parsers; the two round trips and how
they relate; and the theorems that valid modules are well formed.
-/

namespace Fir

open Text

variable {d : Dialect}

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

/--
An item of a dialect's kind can be written and read back: its kind is a
word of a dialect, its parameters' names can be written, each type it
states is written as a type and decodes back to itself, and its attributes
can be written. Its symbol can be any string.
-/
structure DialectItem.WellFormed (i : DialectItem d) : Prop where
  kind : isDialectWord i.kind
  names : ∀ x ∈ i.params, isName x.1
  types : ∀ t ∈ i.types, (tyAttr t).IsType ∧ decodeTy (tyAttr t) = some t
  attrs : Attr.AllWritable i.attrs

mutual
/-- An item can be written and read back: a function that can, a nested
module whose dialect set names each dialect by a word and whose items can,
or an item of a dialect's kind that can. -/
def Item.WellFormed : Item d → Prop
  | .func f => f.WellFormed
  | .module _ ds is => (∀ x ∈ ds, isWord x) ∧ Item.WellFormedList is
  | .dialect i => i.WellFormed

/-- Each of these items can be written and read back. -/
def Item.WellFormedList : List (Item d) → Prop
  | [] => True
  | i :: is => i.WellFormed ∧ Item.WellFormedList is
end

theorem Item.wellFormedList_iff : ∀ is : List (Item d),
    Item.WellFormedList is ↔ ∀ i ∈ is, i.WellFormed
  | [] => by simp [Item.WellFormedList]
  | i :: is => by simp [Item.WellFormedList, Item.wellFormedList_iff is]

/-- A module can be written and read back: each dialect of its set is named
by a word, each of its items can be written and read back, and each number
in its location table is in range. -/
structure Module.WellFormed (m : Module d) : Prop where
  dialects : ∀ x ∈ m.dialects, isWord x
  items : ∀ i ∈ m.items, i.WellFormed
  locs : m.locs.InLimits

/-- Each function of a well-formed module is well formed. -/
theorem Module.WellFormed.funcs {m : Module d} (h : m.WellFormed) : ∀ f ∈ m.funcs, f.WellFormed := by
  intro f hf
  obtain ⟨i, hi, he⟩ := List.mem_filterMap.mp hf
  cases i with
  | func g =>
    cases he
    exact h.items _ hi
  | module | dialect => cases he

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

/-- A function valid in a context whose location references are those of a
valid location table is well formed. -/
theorem Func.Valid.wellFormed {locs : LocTable} {syms : Name → Option (FuncType d)} {f : Func d}
    (hf : f.Valid ⟨syms, locs.map (·.1)⟩) (hl : LocTable.Valid locs) : f.WellFormed := by
  have hdef : ∀ x t, f.typeOf x = some t → isName x := by
    intro x t ht
    unfold Func.typeOf at ht
    cases hp : f.defs.find? (·.1 == x) with
    | none => simp [hp] at ht
    | some p =>
      have hx : (p.1 == x) = true := List.find?_some (p := fun y : Name × d.Ty => y.1 == x) hp
      rw [← beq_iff_eq.mp hx]
      exact hf.names p (List.mem_of_find?_eq_some hp)
  have hgen : ∀ o ∈ f.allOps, f.RegionsValid ⟨syms, locs.map (·.1)⟩ o ∧
      o.operands.map f.typeOf = (sig o.op).map some ∧ o.results.map (·.2) = returnTypes o.op ∧
      (∀ s ∈ o.succs, isName s.label ∧ ∀ a ∈ s.args, isName a) ∧ o.loc ∈ locs.map (·.1) := by
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
    obtain ⟨e, he, hloc⟩ := List.mem_map.mp (show o.loc ∈ locs.map (·.1) from hloc)
    exact hloc ▸ (hl.2.1 e he).1
  · exact ((hgen o ho).1.2 r hr k (Option.mem_def.mp hk)).1

/-- The items of a valid symbol table are well formed when the tables
nested in them are valid too, in a module whose location table is valid. -/
theorem SymbolTable.Valid.itemsWellFormed {locs : LocTable} (hl : LocTable.Valid locs) :
    ∀ (ds : List Name) (is : List (Item d)), SymbolTable.Valid (locs.map (·.1)) ⟨ds, is⟩ →
      (∀ u ∈ Item.tablesIn is, u.Valid (locs.map (·.1))) → ∀ i ∈ is, i.WellFormed
  | _, is, ht, hn, i, hi => by
    cases i with
    | func f => exact Func.Valid.wellFormed (ht.funcs f (List.mem_filterMap.mpr ⟨_, hi, rfl⟩)) hl
    | dialect j =>
      have hv := ht.dialectItems j (List.mem_filterMap.mpr ⟨_, hi, rfl⟩)
      exact ⟨hv.kind, hv.names, fun t h => ⟨LawfulDialectText.tyAttr_isType t (hv.types t h),
        LawfulDialectText.decodeTy_encode t (hv.types t h)⟩, hv.attrs⟩
    | module n ds' js =>
      have hsub := Item.mem_tablesIn hi
      have hv := hn _ (hsub _ (List.mem_cons_self ..))
      rw [Item.WellFormed, Item.wellFormedList_iff]
      exact ⟨hv.dialectNames, SymbolTable.Valid.itemsWellFormed hl ds' js hv
        fun u hu => hn u (hsub u (List.mem_cons_of_mem _ hu))⟩
termination_by _ is => sizeOf is
decreasing_by
  have := List.sizeOf_lt_of_mem hi
  simp only [Item.module.sizeOf_spec] at this
  omega

/-- Every valid module of a dialect with lawful text is well formed. -/
theorem validIsWellFormed : ValidIsWellFormed (d := d) :=
  fun m hm => ⟨hm.dialectNames,
    SymbolTable.Valid.itemsWellFormed hm.locs m.dialects m.items hm.table
      (fun u hu => hm.tables u (List.mem_cons_of_mem _ hu)),
    hm.locs.2.1⟩

end Fir
