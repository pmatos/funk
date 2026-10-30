import Fir.Text.Read

/-!
The location table has a fixed syntax, the same for every dialect, so the
grammar step reads it in full. Its numbers are checked against their limits
(N3) where they stand: a line or a column of `2^32` or more is an error at
the number. Whether the table is well formed, with its references in order
and each location built from earlier ones, is a rule of validation.
-/

namespace Fir.Text

/-- Reads a line or a column: a number below `2^32`. -/
def readNat (what : String) : (ts : List Token) → Read Nat ts
  | ⟨.int (.ofNat n), p⟩ :: rest =>
    if n < Location.limit then .ok (n, ⟨rest, Nat.le_succ _⟩)
    else .error ⟨p, s!"{what} {n} is out of range: it must be below 2^32"⟩
  | ts => fail ts what

/-- Reads a location reference inside a location. -/
def readLocRef : (ts : List Token) → Read LocRef ts
  | ⟨.locRef r, _⟩ :: rest => .ok (r, ⟨rest, Nat.le_succ _⟩)
  | ts => fail ts "a location reference, such as @0"

/-- Reads `, @N` as long as a comma follows. -/
def readMoreLocRefs : (ts : List Token) → Read (List LocRef) ts
  | ⟨.comma, _⟩ :: rest => do
    let (r, ⟨a, ha⟩) ← readLocRef rest
    let (rs, ⟨b, hb⟩) ← readMoreLocRefs a
    pure (r :: rs, ⟨b, by simp; omega⟩)
  | ts => .ok ([], .here ts)
termination_by ts => ts.length

/-- Reads a source range after its file: `:l:c to l:c`. -/
def readRange (file : String) (ts : List Token) : Read Location ts := do
  let ((), a) ← expect .colon ": after the file" ts
  let (l₁, b) ← readNat "a line" a.1
  let ((), c) ← expect .colon ":" b.1
  let (c₁, d) ← readNat "a column" c.1
  let ((), e) ← keyword "to" d.1
  let (l₂, f) ← readNat "a line" e.1
  let ((), g) ← expect .colon ":" f.1
  let (c₂, h) ← readNat "a column" g.1
  pure (.range file l₁ c₁ l₂ c₂, a.then (b.then (c.then (d.then (e.then (f.then (g.then h)))))))

/-- Reads the parenthesized part of a location of kind `kind`, after its
`(`, through its `)`. -/
def readLocArgs (kind : String) (ts : List Token) : Read Location ts := do
  let (loc, a) ← (match kind with
    | "name" => (match ts with
      | ⟨.str n, _⟩ :: rest => pure (Location.name n, ⟨rest, Nat.le_succ _⟩)
      | ts => fail ts "the name, as a string" : Read Location ts)
    | "callsite" => do
      let (callee, a) ← readLocRef ts
      let ((), b) ← keyword "at" a.1
      let (caller, c) ← readLocRef b.1
      pure (.callsite callee caller, a.then (b.then c))
    | "fused" => (match ts with
      | ⟨.rparen, p⟩ :: tl => pure (.fused [], .here (⟨.rparen, p⟩ :: tl))
      | ts' => do
        let (r, a) ← readLocRef ts'
        let (rs, b) ← readMoreLocRefs a.1
        pure (.fused (r :: rs), a.then b) : Read Location ts)
    | _ => do
      let (src, a) ← readLocRef ts
      pure (.derived src, a) : Read Location ts)
  let ((), b) ← expect .rparen ")" a.1
  pure (loc, a.then b)

/-- Reads a location: `unknown`, a source range, or a location built from
others. -/
def readLocation : (ts : List Token) → Read Location ts
  | ⟨.str file, _⟩ :: rest => do
    let (l, a) ← readRange file rest
    pure (l, a.next)
  | ⟨.word "unknown", _⟩ :: rest => .ok (.unknown, ⟨rest, Nat.le_succ _⟩)
  | ⟨.word kind, p⟩ :: rest =>
    if kind ∈ ["name", "callsite", "fused", "derived"] then do
      let ((), a) ← expect .lparen "(" rest
      let (l, b) ← readLocArgs kind a.1
      pure (l, (a.then b).next)
    else .error ⟨p, kind ++ " is not a kind of location"⟩
  | ts => fail ts "a location"

/-- Reads the entries of the location table, as long as a location
reference follows. -/
def readLocEntries : (ts : List Token) → Read LocTable ts
  | ⟨.locRef r, _⟩ :: rest => do
    let ((), ⟨a, ha⟩) ← expect .eq "= after the location reference" rest
    let (l, ⟨b, hb⟩) ← readLocation a
    let (es, ⟨c, hc⟩) ← readLocEntries b
    pure ((r, l) :: es, ⟨c, by simp; omega⟩)
  | ts => .ok ([], .here ts)
termination_by ts => ts.length

/-- Reads the location table: `locs { ... }`. -/
def readLocs (ts : List Token) : Read LocTable ts := do
  let ((), a) ← keyword "locs" ts
  let ((), b) ← expect .lbrace "{ to open the location table" a.1
  let (es, c) ← readLocEntries b.1
  let ((), d) ← expect .rbrace "an entry, such as `@0 = unknown`, or }" c.1
  pure (es, a.then (b.then (c.then d)))

/-!
# A module

A module is its items, then its location table, then the end of the text.
-/

/-- Reads a module from its tokens. -/
def readModule (ts : List Token) : Except ParseError SModule := do
  let (items, a) ← readItems true ts
  match a.1 with
  | ts'@(⟨.word "locs", _⟩ :: _) => do
    let (locs, b) ← readLocs ts'
    let ((), _) ← expect .eof "the end of the text after the location table" b.1
    pure ⟨items, locs⟩
  | ts' => fail ts' "an item or the location table, `locs { ... }`"

end Fir.Text
