import Fir.Text.LexModule

/-!
# Well-formed modules lex

Every token of a well-formed module can be written
(`Module.WellFormed.tokens_writable`): its value names and labels are names,
its op names and the words of its attributes and types are words, and its
location references, on ops and inside locations, are below `2^32`
(`LocTable.InLimits`, through `Location.numbers`). An operand is a name
because its function defines it, and every definition is a name. So the
lexer reads the printed text of every well-formed module as its tokens
(`Module.WellFormed.lex_print`), and through `validIsWellFormed`, of every
valid module of a dialect with lawful text.
-/

namespace Fir

open Text

/-- Every token of a list written with separators can be written when the
separator's and each element's can. -/
theorem forall_mem_intercalate_of {P : Tok → Prop} {sep : List Tok} (hs : ∀ t ∈ sep, P t) :
    ∀ {tss : List (List Tok)}, (∀ ts ∈ tss, ∀ t ∈ ts, P t) → ∀ t ∈ sep.intercalate tss, P t
  | [], _ => by simp
  | [ts], h => by simpa using h ts (.head _)
  | ts :: ts' :: tss, h => by
    rw [List.intercalate_cons_cons]
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · rcases List.mem_append.mp ht with ht | ht
      · exact h ts (.head _) t ht
      · exact hs t ht
    · exact forall_mem_intercalate_of hs (fun us hus => h us (.tail _ hus)) t ht

theorem comma_writable : ∀ t ∈ [Tok.comma], t.Writable := by simp [Tok.Writable]

/-- Splits a goal that every token of a list can be written into a goal for
each part of the list that is not punctuation. -/
local macro "split_writable" : tactic => `(tactic| (
  try simp only [List.forall_mem_cons, List.forall_mem_append, List.forall_mem_flatMap,
    List.not_mem_nil, false_implies, forall_const, Tok.Writable, and_true, true_and]
  try and_intros))

mutual
/-- The tokens of an attribute that can be written can be written. -/
theorem Attr.Writable.tokens : ∀ {a : Attr}, a.Writable → ∀ t ∈ a.tokens, t.Writable
  | .word _, h => fun t ht => by
    simp only [Attr.tokens, List.mem_singleton] at ht
    subst ht
    exact h
  | .int _, _ => by simp [Attr.tokens, Tok.Writable]
  | .str _, _ => by simp [Attr.tokens, Tok.Writable]
  | .sym _, _ => by simp [Attr.tokens, Tok.Writable]
  | .app _ args, h => by
    have hargs := Attr.AllWritable.tokens (as := args) h.2
    simp only [Attr.tokens]
    split_writable
    · exact h.1
    · exact forall_mem_intercalate_of comma_writable hargs

/-- The tokens of attributes that can be written can be written. -/
theorem Attr.AllWritable.tokens : ∀ {as : List Attr}, Attr.AllWritable as →
    ∀ ts ∈ Attr.tokens.tokensList as, ∀ t ∈ ts, t.Writable
  | [], _ => by simp [Attr.tokens.tokensList]
  | _ :: _, h => by
    simp only [Attr.tokens.tokensList, List.forall_mem_cons]
    exact ⟨Attr.Writable.tokens h.1, Attr.AllWritable.tokens h.2⟩
end

/-- Each attribute of a list that can be written can be written. -/
theorem Attr.AllWritable.mem : ∀ {as : List Attr}, Attr.AllWritable as → ∀ a ∈ as, a.Writable
  | [], _, _, ha => by simp at ha
  | _ :: _, h, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact Attr.AllWritable.mem h.2 a ha

/-- A type is an attribute that can be written. -/
theorem Attr.IsType.writable : ∀ {a : Attr}, a.IsType → a.Writable
  | .word _, h | .app .., h => h

/-- The tokens of a location in a table within the limits can be written. -/
theorem Location.tokens_writable (l : Location) (h : ∀ n ∈ l.numbers, n < Location.limit) :
    ∀ t ∈ l.tokens, t.Writable := by
  cases l with
  | fused locs =>
    simp only [Location.tokens]
    split_writable
    · decide
    · refine forall_mem_intercalate_of comma_writable fun ts hts => ?_
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hts
      simpa [Tok.Writable] using h r (by simpa [Location.numbers, Location.refs] using hr)
  | callsite callee caller =>
    simp only [Location.tokens]
    split_writable
    · decide
    · exact h callee (by simp [Location.numbers, Location.refs])
    · decide
    · exact h caller (by simp [Location.numbers, Location.refs])
  | derived src =>
    simp only [Location.tokens]
    split_writable
    · decide
    · exact h src (by simp [Location.numbers, Location.refs])
  | _ => simp only [Location.tokens]; split_writable <;> decide

/-- The tokens of a location table within the limits can be written. -/
theorem LocTable.InLimits.tokens {t : LocTable} (h : t.InLimits) : ∀ x ∈ t.tokens, x.Writable := by
  simp only [LocTable.tokens]
  split_writable
  · decide
  · intro e he
    split_writable
    · exact (h e he).1
    · exact Location.tokens_writable e.2 (h e he).2

variable {d : Dialect} [DialectSignature d] [DialectText d]

omit [DialectSignature d] [DialectText d] in
/-- An op's regions hold blocks below the op's block. -/
theorem regionBlocks_of_mem {o : Operation d} :
    ∀ {os : List (Operation d)}, o ∈ os →
      ∀ b ∈ Region.allBlocks o.regions, b ∈ Operation.regionBlocks os
  | ⟨_, _, _, _, _, _⟩ :: _, ho, b, hb => by
    rcases List.mem_cons.mp ho with rfl | ho
    · simp [Operation.regionBlocks, hb]
    · simp [Operation.regionBlocks, regionBlocks_of_mem ho b hb]

namespace Func.WellFormed

variable {f : Func d}

/-- The tokens of a definition of the function can be written. -/
theorem def_tokens (hf : f.WellFormed) {x : Name × d.Ty} (hx : x ∈ f.defs) :
    ∀ t ∈ defTokens x, t.Writable := by
  have hty : x.2 ∈ f.types := List.mem_append_right _ (List.mem_map_of_mem hx)
  simp only [defTokens]
  split_writable
  · exact hf.names x hx
  · exact Attr.Writable.tokens (hf.types x.2 hty).1.writable

/-- The tokens of definitions of the function can be written. -/
theorem defs_tokens (hf : f.WellFormed) {xs : List (Name × d.Ty)} (hxs : ∀ x ∈ xs, x ∈ f.defs) :
    ∀ t ∈ defsTokens xs, t.Writable :=
  forall_mem_intercalate_of comma_writable fun ts hts => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hts
    exact hf.def_tokens (hxs x hx)

/-- A value that the function defines is a name. -/
theorem isName_of_typeOf (hf : f.WellFormed) {x : Name} {t : d.Ty} (h : f.typeOf x = some t) :
    isName x = true := by
  unfold Func.typeOf at h
  cases hp : f.defs.find? (·.1 == x) with
  | none => simp [hp] at h
  | some p =>
    have hx : (p.1 == x) = true := List.find?_some (p := fun y : Name × d.Ty => y.1 == x) hp
    rw [← beq_iff_eq.mp hx]
    exact hf.names p (List.mem_of_find?_eq_some hp)

/-- The tokens of an op's name, attributes, operands and successors can be
written. -/
theorem rhs_tokens (hf : f.WellFormed) {o : Operation d} (ho : f.OpWellFormed o) :
    ∀ t ∈ (if (o.operands.map ([Tok.value ·]) ++ o.succs.map Succ.tokens).isEmpty = true then
        Tok.word (opName o.op) :: (opAttrs o.op).flatMap Attr.tokens
      else Tok.word (opName o.op) :: (opAttrs o.op).flatMap Attr.tokens ++
        [Tok.comma].intercalate (o.operands.map ([Tok.value ·]) ++ o.succs.map Succ.tokens)),
      t.Writable := by
  obtain ⟨hname, hattrs, hops, -, hsuccs, -⟩ := ho
  have hhead : ∀ t ∈ Tok.word (opName o.op) :: (opAttrs o.op).flatMap Attr.tokens, t.Writable := by
    simp only [List.forall_mem_cons, List.forall_mem_flatMap]
    exact ⟨hname, fun a ha => Attr.Writable.tokens (hattrs.mem a ha)⟩
  split
  · exact hhead
  · refine List.forall_mem_append.mpr ⟨hhead, forall_mem_intercalate_of comma_writable ?_⟩
    intro ts hts
    rcases List.mem_append.mp hts with hts | hts
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hts
      have : f.typeOf x ∈ (sig o.op).map some := hops ▸ List.mem_map_of_mem hx
      obtain ⟨t, -, ht⟩ := List.mem_map.mp this
      simpa [Tok.Writable] using hf.isName_of_typeOf ht.symm
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hts
      obtain ⟨hl, ha⟩ := hsuccs s hs
      simp only [Succ.tokens, List.forall_mem_cons]
      refine ⟨hl, ?_⟩
      split
      · simp
      · split_writable
        refine forall_mem_intercalate_of comma_writable fun us hus => ?_
        obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hus
        simpa [Tok.Writable] using ha a hmem

/-- The tokens of an op's results and its `=` can be written. -/
theorem lhs_tokens (hf : f.WellFormed) {results : List (Name × d.Ty)}
    (hres : ∀ x ∈ results, x ∈ f.defs) :
    ∀ t ∈ (if results.isEmpty = true then [] else defsTokens results ++ [Tok.eq]), t.Writable := by
  split
  · simp
  · split_writable
    exact hf.defs_tokens hres

mutual
/-- The tokens of blocks of the function, at any depth, can be written. -/
theorem blocks_tokens (hf : f.WellFormed) :
    ∀ bs : List (Block d), (∀ b ∈ Block.allBlocks bs, b ∈ f.allBlocks) →
    ∀ t ∈ Block.tokensList bs, t.Writable
  | [], _ => by simp [Block.tokensList]
  | ⟨label, params, body⟩ :: bs, hsub => by
    have hb : (⟨label, params, body⟩ : Block d) ∈ f.allBlocks := hsub _ (by simp [Block.allBlocks])
    have hdefs : ∀ x ∈ Block.defs ⟨label, params, body⟩, x ∈ f.defs := fun x hx =>
      List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hb, hx⟩)
    have hops := ops_tokens hf body
      (fun o ho => ⟨List.mem_flatMap.mpr ⟨_, hb, ho⟩,
        fun x hx => hdefs x (List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ho, hx⟩))⟩)
      (fun b hb' => hsub b (by simp [Block.allBlocks, hb']))
    have hbs := blocks_tokens hf bs fun b hb' => hsub b (by simp [Block.allBlocks, hb'])
    have hps : ∀ t ∈ (if params.isEmpty = true then [] else .lparen :: defsTokens params ++ [.rparen]),
        t.Writable := by
      split
      · simp
      · split_writable
        exact hf.defs_tokens fun x hx => hdefs x (List.mem_append_left _ hx)
    simp only [Block.tokensList]
    split_writable
    · exact hf.labels _ hb
    · exact hps
    · exact hops
    · exact hbs

/-- The tokens of ops of the function, at any depth, can be written. -/
theorem ops_tokens (hf : f.WellFormed) : ∀ os : List (Operation d),
    (∀ o ∈ os, o ∈ f.allOps ∧ ∀ x ∈ o.results, x ∈ f.defs) →
    (∀ b ∈ Operation.regionBlocks os, b ∈ f.allBlocks) → ∀ t ∈ Operation.tokensList os, t.Writable
  | [], _, _ => by simp [Operation.tokensList]
  | ⟨results, op, operands, succs, regions, loc⟩ :: os, h, hsub => by
    have ho := h _ (.head _)
    simp only [Operation.tokensList, List.forall_mem_append]
    exact ⟨op_tokens hf _ ho.1 ho.2 fun b hb => hsub b (by simp [Operation.regionBlocks, hb]),
      ops_tokens hf os (fun o' ho' => h o' (.tail _ ho'))
        fun b hb => hsub b (by simp [Operation.regionBlocks, hb])⟩

/-- The tokens of an op of the function, at any depth, can be written. -/
theorem op_tokens (hf : f.WellFormed) :
    ∀ o : Operation d, o ∈ f.allOps → (∀ x ∈ o.results, x ∈ f.defs) →
    (∀ b ∈ Region.allBlocks o.regions, b ∈ f.allBlocks) → ∀ t ∈ o.tokens, t.Writable
  | ⟨results, op, operands, succs, regions, loc⟩, ho, hres, hsub => by
    have hwf := hf.ops _ ho
    have hregs := regions_tokens hf regions hsub
    simp only [Operation.tokens]
    split_writable
    · exact hf.lhs_tokens hres
    · exact hf.rhs_tokens hwf
    · exact hregs
    · exact hwf.2.2.2.2.2

/-- The tokens of regions of the function, at any depth, can be written. -/
theorem regions_tokens (hf : f.WellFormed) :
    ∀ rs : List (Region d), (∀ b ∈ Region.allBlocks rs, b ∈ f.allBlocks) →
    ∀ t ∈ Region.tokensList rs, t.Writable
  | [], _ => by simp [Region.tokensList]
  | ⟨bs⟩ :: rs, hsub => by
    have h₁ := blocks_tokens hf bs fun b hb => hsub b (by simp [Region.allBlocks, hb])
    have h₂ := regions_tokens hf rs fun b hb => hsub b (by simp [Region.allBlocks, hb])
    simp only [Region.tokensList]
    split_writable
    · exact h₁
    · exact h₂
end

/-- Every token of a well-formed function can be written. -/
theorem tokens (hf : f.WellFormed) : ∀ t ∈ f.tokens, t.Writable := by
  have hblocks := hf.blocks_tokens f.body.blocks fun b hb => hb
  have hres : ∀ t ∈ (if f.results.isEmpty = true then []
      else Tok.arrow :: [Tok.comma].intercalate (f.results.map (tyAttr · |>.tokens))), t.Writable := by
    split
    · simp
    · split_writable
      refine forall_mem_intercalate_of comma_writable fun ts hts => ?_
      obtain ⟨ty, hty, rfl⟩ := List.mem_map.mp hts
      exact Attr.Writable.tokens (hf.types ty (List.mem_append_left _ hty)).1.writable
  simp only [Func.tokens]
  split_writable
  · decide
  · exact hf.defs_tokens fun x hx => List.mem_append_left _ hx
  · exact hres
  · exact hblocks

end Func.WellFormed

/-- Every token of a well-formed module can be written. -/
theorem Module.WellFormed.tokens_writable {m : Module d} (h : m.WellFormed) :
    ∀ t ∈ m.tokens, t.Writable := by
  simp only [Module.tokens, List.forall_mem_append, List.forall_mem_flatMap]
  refine ⟨fun i hi => ?_, h.locs.tokens⟩
  cases i with
  | func f => exact (h.funcs f (List.mem_map.mpr ⟨_, hi, rfl⟩)).tokens

/-- The lexer reads the printed text of a well-formed module as its tokens. -/
theorem Module.WellFormed.lex_print {m : Module d} (h : m.WellFormed) :
    ∃ ts, lex m.print = .ok ts ∧ ts.map (·.tok) = m.tokens ++ [.eof] :=
  Fir.lex_print h.tokens_writable

/-- The lexer reads the printed text of a valid module of a dialect with
lawful text as its tokens. -/
theorem Module.Valid.lex_print [DialectValidation d] [LawfulDialectText d] {m : Module d}
    (h : m.Valid) : ∃ ts, lex m.print = .ok ts ∧ ts.map (·.tok) = m.tokens ++ [.eof] :=
  (validIsWellFormed m h).lex_print

end Fir
