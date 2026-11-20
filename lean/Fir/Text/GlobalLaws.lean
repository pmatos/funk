import Fir.Text.GlobalText
import Fir.Text.LayoutLaws

/-!
# Globals in text, proved

A global has one spelling: decoding the attributes it writes gives it back
when its numbers are within the limit, and attributes decode only to a
global whose numbers are within it. Every attribute a global writes can be
written, whatever its numbers and symbols (ADR-2026-11-09-1546).
-/

namespace Fir

/-- Units written one by one can be written. -/
theorem InitPiece.units_writable :
    ∀ us : List Nat, Attr.AllWritable (us.map fun (u : Nat) => Attr.int u)
  | [] => trivial
  | _ :: us => ⟨trivial, InitPiece.units_writable us⟩

/-- Every piece of an initializer can be written. -/
theorem InitPiece.attr_writable : ∀ p : InitPiece, p.attr.Writable
  | .units us => ⟨by decide, InitPiece.units_writable us⟩
  | .zeros _ => ⟨by decide, trivial, trivial⟩
  | .addr _ k => by
    by_cases hk : k = 0
    · simp only [InitPiece.attr, hk, ↓reduceIte]
      exact ⟨by decide, trivial, trivial⟩
    · simp only [InitPiece.attr, hk, ↓reduceIte]
      exact ⟨by decide, trivial, trivial, trivial⟩

/-- Every attribute that a global writes can be written. -/
theorem Global.attr_writable (g : Global) : ∀ a ∈ g.attrs, a.Writable := by
  intro a ha
  unfold Global.attrs at ha
  rcases List.mem_append.mp ha with ha | ha
  · split at ha
    · cases ha
    · rw [List.mem_singleton] at ha
      subst ha
      exact ⟨by decide, trivial, trivial⟩
  rcases List.mem_cons.mp ha with rfl | ha
  · exact ⟨by decide, trivial, trivial⟩
  rcases List.mem_cons.mp ha with rfl | ha
  · exact ⟨by decide, trivial, trivial⟩
  rcases List.mem_append.mp ha with ha | ha
  · split at ha
    · rw [List.mem_singleton] at ha
      subst ha
      exact (by decide : isWord "const")
    · cases ha
  rcases List.mem_append.mp ha with ha | ha
  · split at ha
    · rw [List.mem_singleton] at ha
      subst ha
      exact (by decide : isWord "export")
    · cases ha
  · obtain ⟨p, -, rfl⟩ := List.mem_map.mp ha
    exact InitPiece.attr_writable p

/-- Units written one by one decode back. -/
theorem InitPiece.decodeUnits_map : ∀ us : List Nat,
    (us.map fun (u : Nat) => Attr.int u).mapM InitPiece.decodeUnit = some us
  | [] => rfl
  | u :: us => by
    rw [List.map_cons, List.mapM_cons, InitPiece.decodeUnits_map us]
    simp [InitPiece.decodeUnit]

theorem InitPiece.decode_units (us : List Nat) :
    InitPiece.decode (InitPiece.attr (.units us)) = some (.units us) := by
  simp only [InitPiece.attr, InitPiece.decode, ↓reduceIte, InitPiece.decodeUnits_map,
    Option.map_some]

theorem InitPiece.decode_zeros {n : Nat} (h : n ≤ Aggregate.limit) :
    InitPiece.decode (InitPiece.attr (.zeros n)) = some (.zeros n) := by
  simp only [InitPiece.attr, InitPiece.decode, String.reduceEq, ↓reduceIte,
    Aggregate.number_ofNat h, Option.map_some]

theorem InitPiece.decode_addr_zero (s : Name) :
    InitPiece.decode (InitPiece.attr (.addr s 0)) = some (.addr s 0) := by
  simp only [InitPiece.attr, InitPiece.decode, String.reduceEq, ↓reduceIte]

theorem InitPiece.decode_addr_succ (s : Name) {k : Nat} (h : k + 1 ≤ Aggregate.limit) :
    InitPiece.decode (InitPiece.attr (.addr s (k + 1))) = some (.addr s (k + 1)) := by
  simp only [InitPiece.attr, Nat.add_one_ne_zero, ↓reduceIte, InitPiece.decode,
    String.reduceEq, Aggregate.number_ofNat h, Option.bind_some]

/-- A piece decodes back from what it writes, when its numbers are within
the limit. -/
theorem InitPiece.decode_attr : ∀ {p : InitPiece}, p.InLimits → InitPiece.decode p.attr = some p
  | .units us, _ => InitPiece.decode_units us
  | .zeros _, h => InitPiece.decode_zeros h
  | .addr s 0, _ => InitPiece.decode_addr_zero s
  | .addr s (_ + 1), h => InitPiece.decode_addr_succ s h

/-- A piece that decodes has its numbers within the limit. -/
theorem InitPiece.inLimits_of_decode {a : Attr} {p : InitPiece} (h : InitPiece.decode a = some p) :
    p.InLimits := by
  unfold InitPiece.decode at h
  split at h
  · split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨_, -, rfl⟩ := h
      trivial
    · split at h
      · split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨n, hn, rfl⟩ := h
          exact Aggregate.le_of_number hn
        · cases h
      · split at h
        · split at h
          · cases h
            exact Nat.zero_le _
          · simp only [Option.bind_eq_some_iff] at h
            obtain ⟨k, hk, h⟩ := h
            split at h
            · cases h
            · cases h
              exact Aggregate.le_of_number hk
          · cases h
        · cases h
  · cases h

/-- Pieces decode back from what they write when their numbers are within
the limit. -/
theorem InitPiece.mapM_decode_attr : ∀ {ps : List InitPiece}, (∀ p ∈ ps, p.InLimits) →
    (ps.map InitPiece.attr).mapM InitPiece.decode = some ps
  | [], _ => rfl
  | p :: ps, h => by
    simp only [List.map_cons, List.mapM_cons, InitPiece.decode_attr (h p (.head _)),
      InitPiece.mapM_decode_attr fun q hq => h q (.tail _ hq)]
    rfl

/-- Pieces decode back from what they write, at any index, when their
numbers are within the limit. -/
theorem Global.decodePieces_map {ps : List InitPiece} (i : Nat) (h : ∀ p ∈ ps, p.InLimits) :
    Global.decodePieces i (ps.map InitPiece.attr) = .ok ps := by
  simp only [Global.decodePieces, InitPiece.mapM_decode_attr h]

/-- Pieces that decode one by one have their numbers within the limit. -/
theorem InitPiece.inLimits_of_mapM_decode : ∀ {as : List Attr} {ps : List InitPiece},
    as.mapM InitPiece.decode = some ps → ∀ p ∈ ps, p.InLimits
  | [], ps, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp
  | a :: as, ps, h => by
    cases hd : InitPiece.decode a with
    | none => simp [List.mapM_cons, hd] at h
    | some p =>
      cases hr : as.mapM InitPiece.decode with
      | none => simp [List.mapM_cons, hd, hr] at h
      | some qs =>
        simp only [List.mapM_cons, hd, hr, Option.bind_some, Option.some.injEq, bind,
          pure] at h
        subst h
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact InitPiece.inLimits_of_decode hd
        · exact InitPiece.inLimits_of_mapM_decode hr q hq

/-- Pieces that decode have their numbers within the limit. -/
theorem Global.inLimits_of_decodePieces {as : List Attr} {i : Nat} {ps : List InitPiece}
    (h : Global.decodePieces i as = .ok ps) : ∀ p ∈ ps, p.InLimits := by
  unfold Global.decodePieces at h
  split at h
  · rename_i qs hq
    cases h
    exact InitPiece.inLimits_of_mapM_decode hq
  · cases h

/-- The words that a global may write after its alignment read back. -/
theorem Global.decodeFlag_const (c : Bool) (rest : List Attr)
    (hr : ∀ w r, rest = .word w :: r → w ≠ "const") :
    Global.decodeFlag "const" ((if c then [.word "const"] else []) ++ rest) = (c, rest) := by
  cases c with
  | true => simp [Global.decodeFlag]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    match rest, hr with
    | .word w :: r, hr => simp [Global.decodeFlag, hr w r rfl]
    | [], _ | .int _ :: _, _ | .str _ :: _, _ | .sym _ :: _, _ | .app .. :: _, _
    | .float _ :: _, _ => rfl

theorem Global.decodeFlag_export (e : Bool) (rest : List Attr)
    (hr : ∀ w r, rest = .word w :: r → w ≠ "export") :
    Global.decodeFlag "export" ((if e then [.word "export"] else []) ++ rest) = (e, rest) := by
  cases e with
  | true => simp [Global.decodeFlag]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    match rest, hr with
    | .word w :: r, hr => simp [Global.decodeFlag, hr w r rfl]
    | [], _ | .int _ :: _, _ | .str _ :: _, _ | .sym _ :: _, _ | .app .. :: _, _
    | .float _ :: _, _ => rfl

/-- What pieces write starts with no word. -/
theorem InitPiece.map_attr_head (ps : List InitPiece) :
    ∀ w r, ps.map InitPiece.attr = .word w :: r → False := by
  intro w r h
  cases ps with
  | nil => cases h
  | cons p _ => cases p <;> simp [InitPiece.attr] at h

/-- A global of memory 0 writes no memory. -/
theorem Global.decodeMem_size (z : Int) (r : List Attr) :
    Global.decodeMem (.app "size" [.int z] :: r) = .ok (0, 0, .app "size" [.int z] :: r) := by
  simp only [Global.decodeMem, String.reduceEq, ↓reduceIte]

/-- Another global writes its memory first. -/
theorem Global.decodeMem_memory {n : Nat} (h : n ≤ Aggregate.limit) (hn : n ≠ 0) (r : List Attr) :
    Global.decodeMem (.app "memory" [.int n] :: r) = .ok (n, 1, r) := by
  simp only [Global.decodeMem, ↓reduceIte, Aggregate.decodeNumber_app _ h, hn]

/-- A global decodes back from the attributes it writes, when its numbers
are within the limit. -/
theorem Global.decodeAttrs_attrs {g : Global} (h : g.InLimits) :
    Global.decodeAttrs g.name g.attrs = .ok g := by
  obtain ⟨name, mem, size, align, c, lk, init⟩ := g
  obtain ⟨hm, hs, ha, hp⟩ := h
  simp only at hm hs ha hp
  have hE : ∃ e : Bool, (if lk = .exported then [Attr.word "export"] else []) =
      (if e then [.word "export"] else []) ∧ (if e then Linkage.exported else .internal) = lk :=
    match lk with
    | .exported => ⟨true, rfl, rfl⟩
    | .internal => ⟨false, rfl, rfl⟩
  obtain ⟨e, he, hlk⟩ := hE
  have hc : ∀ w r, (if e then [Attr.word "export"] else []) ++ init.map InitPiece.attr =
      .word w :: r → w ≠ "const" := by
    intro w r hw
    cases e with
    | true =>
      simp only [↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq,
        Attr.word.injEq] at hw
      rw [← hw.1]
      simp only [ne_eq, String.reduceEq, not_false_eq_true]
    | false => exact (InitPiece.map_attr_head _ w r hw).elim
  have hrest : ∀ i, (do
      let (c', rest) := Global.decodeFlag "const" ((if c then [Attr.word "const"] else []) ++
        ((if lk = .exported then [Attr.word "export"] else []) ++ init.map InitPiece.attr))
      let (e', rest) := Global.decodeFlag "export" rest
      let init' ← Global.decodePieces (i + 2 + c'.toNat + e'.toNat) rest
      pure (⟨name, mem, size, align, c', if e' then .exported else .internal, init'⟩ : Global) :
        Except GlobalFault Global) = .ok ⟨name, mem, size, align, c, lk, init⟩ := by
    intro i
    rw [he, Global.decodeFlag_const c _ hc]
    dsimp only
    rw [Global.decodeFlag_export e _ (fun w r hw => (InitPiece.map_attr_head _ w r hw).elim)]
    dsimp only
    rw [Global.decodePieces_map _ hp]
    simp only [hlk]
    rfl
  by_cases hz : mem = 0
  · subst hz
    simp only [Global.decodeAttrs, Global.attrs, ↓reduceIte, List.nil_append,
      Global.decodeMem_size, bind, Except.bind, Aggregate.decodeNumber_app _ hs,
      Aggregate.decodeNumber_app _ ha]
    exact hrest 0
  · simp only [Global.decodeAttrs, Global.attrs, hz, ↓reduceIte, List.cons_append,
      List.nil_append, Global.decodeMem_memory hm hz, bind, Except.bind,
      Aggregate.decodeNumber_app _ hs, Aggregate.decodeNumber_app _ ha]
    exact hrest 1

/-- A global that decodes has its numbers within the limit. -/
theorem Global.inLimits_of_decodeAttrs {n : Name} {as : List Attr} {g : Global}
    (h : Global.decodeAttrs n as = .ok g) : g.InLimits := by
  unfold Global.decodeAttrs at h
  cases hm : Global.decodeMem as with
  | error e => rw [hm] at h; cases h
  | ok r =>
    obtain ⟨mem, i, rest⟩ := r
    rw [hm] at h
    have hmem : mem ≤ Aggregate.limit := by
      unfold Global.decodeMem at hm
      split at hm
      · split at hm
        · split at hm
          · rename_i hd
            split at hm
            · cases hm
            · cases hm
              exact Aggregate.le_of_decodeNumber hd
          · cases hm
        · cases hm; exact Nat.zero_le _
      · cases hm; exact Nat.zero_le _
    simp only [bind, Except.bind] at h
    split at h
    · split at h
      · rename_i hs ha
        split at h
        · cases h
        · rename_i ps hps
          cases h
          exact ⟨hmem, Aggregate.le_of_decodeNumber hs, Aggregate.le_of_decodeNumber ha,
            Global.inLimits_of_decodePieces hps⟩
      · cases h
      · cases h
    · cases h

/-- A global that decodes has the symbol it was decoded with. -/
theorem Global.name_of_decodeAttrs {n : Name} {as : List Attr} {g : Global}
    (h : Global.decodeAttrs n as = .ok g) : g.name = n := by
  unfold Global.decodeAttrs at h
  cases hm : Global.decodeMem as with
  | error e => rw [hm] at h; cases h
  | ok r =>
    rw [hm] at h
    simp only [bind, Except.bind] at h
    split at h
    · split at h
      · split at h
        · cases h
        · cases h; rfl
      · cases h
      · cases h
    · cases h

end Fir
