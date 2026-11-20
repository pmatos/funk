import FirRef.Run

/-!
The command line of `fir-ref run`
(`docs/decisions/fir-ref-command-line.md#fir-ref-run`):

`fir-ref run [--fuel N] [--choices C,C,... | --exhaustive [--choice-bits B] [--nans V,V,...]
| --seed S]
[--work-item-id X,Y,Z] [--work-group-id X,Y,Z] [--work-group-size X,Y,Z]
[--num-work-groups X,Y,Z] [--world WORLD] FILE @FUNC [ARG...]`

Options may come anywhere before `--`, which ends them, and each takes the
next argument as its value. An argument such as `-5` is not an option.

* `--fuel N`: the fuel budget, N steps.
* `--choices C,C,...`: scripted mode's choice sequence, the choices in the
  order the run makes them, separated by commas, with no spaces. Each is
  spelled as a constant of its choice's type: `true` or `false` at `i1`,
  signed decimal at every other width. The empty text is the empty
  sequence, which is the default.
* `--exhaustive`: exhaustive mode instead of scripted mode.
* `--choice-bits B`: exhaustive mode's choice budget, B bits in all on one
  path; 16 by default.
* `--nans V,V,...`: with `--exhaustive`, try at each NaN choice only the
  positive quiet NaN and each `V` that is a NaN of its format
  (`Gpu.exhaustiveNaN`). Each `V` is a bit pattern, `0x` and lowercase
  hexadecimal digits, separated by commas, with no spaces; the empty text gives none.
* `--seed S`: sampled mode instead of scripted mode: each choice is drawn
  from a generator seeded with S, from 0 to 2^64 - 1.
* `--world WORLD`: the scripted world that the file WORLD holds
  (`FirRef.readWorld`): the run reports the trace of each path and, at a
  return, what escaped and the memory an observer reaches
  (`docs/decisions/fir-ref-run-end.md`).
* `--work-item-id X,Y,Z`, `--work-group-id X,Y,Z`, `--work-group-size X,Y,Z`
  and `--num-work-groups X,Y,Z`: the work-item that the run runs, the input
  that the ops of `gpu` read (`Gpu.WorkItem`), each a number in each of the
  dimensions `gpu.x`, `gpu.y` and `gpu.z`. By default every id is 0 and
  every size 1. The work-item must be one of its grid (`Gpu.WorkItem.Valid`).

N, B, S, X, Y and Z are ASCII decimal digits. `--choices`, `--exhaustive` and
`--seed` go one at a time, and `--choice-bits` and `--nans` need `--exhaustive`.
-/

namespace FirRef

open Fir

/-- The arguments of `run`: its fuel, its mode, its file, the function and
the function's arguments. -/
structure RunArgs where
  fuel : Nat
  mode : Mode
  file : String
  func : String
  args : List String
  workItem : Gpu.WorkItem := .single
  world : Option String := none

/-- The options of `run` read so far. -/
structure RunOptions where
  fuel : Nat := defaultFuel
  choices : Option String := none
  exhaustive : Bool := false
  budget : Option Nat := none
  seed : Option Nat := none
  nans : Option (List Nat) := none
  workItem : Gpu.WorkItem := .single
  world : Option String := none

/-- The number that the value `n` of the option `opt` spells: ASCII decimal
digits. -/
def optionNat (opt what n : String) : Except String Nat :=
  match if n.all Char.isDigit then n.toNat? else none with
  | some k => .ok k
  | none => .error s!"{opt} takes {what}, not {shown n}"

/-- The choices that `--choices` spells: none for the empty text, and
otherwise the texts between its commas. -/
def choiceList (s : String) : List String := if s.isEmpty then [] else s.splitOn ","

/-- The NaNs that `--nans` spells: none for the empty text, and otherwise
the bit pattern between each pair of commas. An error names the first
text that is no bit pattern. -/
def nanList (v : String) : Except String (List Nat) :=
  if v.isEmpty then .ok [] else (v.splitOn ",").mapM fun n => match hexBits n with
    | some b => .ok b
    | none => .error s!"--nans takes bit patterns, as 0x7fc00000,0xffc00000, not {shown n}"

/-- The three numbers that the value `v` of the work-item option `opt`
spells, one per dimension: ASCII decimal digits below 2^32, joined by
commas. -/
def dims (opt v : String) : Except String (Gpu.Dim → Nat) :=
  let why := s!"{opt} takes three numbers below 2^32, as X,Y,Z, not {shown v}"
  match (v.splitOn ",").mapM fun n => if n.all Char.isDigit then n.toNat? else none with
  | some [x, y, z] =>
    if x < 2 ^ 32 ∧ y < 2 ^ 32 ∧ z < 2 ^ 32 then .ok fun | .x => x | .y => y | .z => z
    else .error why
  | _ => .error why

/-- The options that give the work-item, each with the numbers of the
work-item that it sets. -/
def workItemOptions : List (String × (Gpu.WorkItem → (Gpu.Dim → Nat) → Gpu.WorkItem)) :=
  [("--work-item-id", fun w v => { w with itemId := v }),
    ("--work-group-id", fun w v => { w with groupId := v }),
    ("--work-group-size", fun w v => { w with groupSize := v }),
    ("--num-work-groups", fun w v => { w with numGroups := v })]

/-- Why the work-item is not one of its grid, in the first dimension where
it is not. -/
def workItemProblem (w : Gpu.WorkItem) : Option String :=
  if decide w.Valid then none else some <| ([(Gpu.Dim.x, "x"), (.y, "y"), (.z, "z")].findSome?
    fun (d, n) =>
      if w.itemId d ≥ w.groupSize d then
        some s!"the work-item id {w.itemId d} in {n} is not below the work-group size {w.groupSize d}"
      else if w.groupId d ≥ w.numGroups d then
        some s!"the work-group id {w.groupId d} in {n} is not below the number of work-groups {w.numGroups d}"
      else none).getD "the work-item is not one of its grid"

/-- Reads the arguments of `run`. -/
def runArgs (args : List String) : Except String RunArgs := go true {} [] args
where
  go (options : Bool) (o : RunOptions) (pos : List String) : List String → Except String RunArgs
    | [] => do
      let mode ← match o.choices, o.exhaustive, o.budget, o.seed with
        | some _, true, _, _ => .error "--choices does not go with --exhaustive"
        | _, true, _, some _ => .error "--seed does not go with --exhaustive"
        | some _, false, _, some _ => .error "--seed does not go with --choices"
        | _, false, some _, _ => .error "--choice-bits needs --exhaustive"
        | _, false, _, _ => if o.nans.isSome then .error "--nans needs --exhaustive" else
          match o.choices, o.seed with
          | none, some s => .ok (.sampled s)
          | cs, _ => .ok (.scripted (choiceList (cs.getD "")))
        | none, true, b, none => .ok (match o.nans with
          | some ns => .exhaustiveNaN (b.getD defaultChoiceBits) ns
          | none => .exhaustive (b.getD defaultChoiceBits))
      if let some why := workItemProblem o.workItem then .error why
      match pos.reverse with
      | file :: func :: rest => .ok ⟨o.fuel, mode, file, func, rest, o.workItem, o.world⟩
      | [_] => .error "no @FUNC given"
      | [] => .error "no FILE given; use - for standard input"
    | a :: rest =>
      if options && a == "--" then go false o pos rest
      else if options && a == "--exhaustive" then go options { o with exhaustive := true } pos rest
      else if let (some set, true) := (workItemOptions.lookup a, options) then
        match rest with
        | v :: rest' => do go options { o with workItem := set o.workItem (← dims a v) } pos rest'
        | [] => .error s!"{a} takes three numbers below 2^32, as X,Y,Z"
      else if options && (a == "--fuel" || a == "--choices" || a == "--choice-bits" ||
          a == "--seed" || a == "--nans" || a == "--world") then
        match rest with
        | v :: rest' => do
          let o' ← match a with
            | "--fuel" => do pure { o with fuel := ← optionNat a "a number of steps" v }
            | "--choice-bits" => do pure { o with budget := some (← optionNat a "a number of bits" v) }
            | "--seed" => do
              let s ← optionNat a "a number below 2^64" v
              if s < 2 ^ 64 then pure { o with seed := some s }
              else .error s!"--seed takes a number below 2^64, not {shown v}"
            | "--nans" => do pure { o with nans := some (← nanList v) }
            | "--world" => pure { o with world := some v }
            | _ => pure { o with choices := some v }
          go options o' pos rest'
        | [] => .error (match a with
          | "--fuel" => "--fuel takes a number of steps"
          | "--choice-bits" => "--choice-bits takes a number of bits"
          | "--seed" => "--seed takes a number below 2^64"
          | "--nans" => "--nans takes a list of bit patterns"
          | "--world" => "--world takes a file, WORLD"
          | _ => "--choices takes a list of choices")
      else if options && a.startsWith "--" then .error s!"unknown option {shown a}"
      else go options o (a :: pos) rest

/-! # Arguments of a function

Arguments are spelled as constants are in text (`readArg`).
-/

/-- The `const` op that the text `s` spells at the type `t`: the spec's
lexer reads `s` as one token (`argAttr`, which `fir-ref` runs as
`argAttrP`, over positions), `Core.Op.decode` reads that as a `const`, and
the token is spelled exactly `s`, with nothing around it. -/
def constOpOf (t : Core.Ty) (s : String) : Option Core.Op := do
  let attr ← argAttr s
  if attr.print != s then none
  Core.Op.decode "const" [attr] [] [t]

/-- The constant that the text `s` spells at the type `iN` (`constOpOf`). -/
def constOf (w : Nat) (s : String) : Option (BitVec w) :=
  match constOpOf (.int w) s with
  | some (.const w' v) => if h : w' = w then some (h ▸ v) else none
  | _ => none

/-- The constant that the text `s` spells at the float type `float<e,m>`
(`constOpOf`): the one float literal of its bits. -/
def floatConstOf (e m : Nat) (s : String) : Option (BitVec (Core.floatWidth e m)) :=
  match constOpOf (.float e m) s with
  | some (.fconst e' m' v) => if h : e' = e ∧ m' = m then some (h.1 ▸ h.2 ▸ v) else none
  | _ => none

/-- An argument of type `t`: `poison` at any `iN`, any float type and any
`ptr<N>`, or a constant of an `iN` or a float type, spelled as `valueText`
spells it. At `ptr<N>`, `poison` is the only argument: a run starts with no
allocation, so no pointer has provenance for one. A pointer that
`valueText` writes, `ptr(A, O)` or `ptr(none, O)`, is the one value of the
output that is no argument. -/
def readArg : (t : Core.Ty) → String → Except String ⟦t⟧
  | .int w, "poison" => pure (.poison : PoisonOr (BitVec w))
  | .int w, s => match constOf w s with
    | some v => pure (.value v : PoisonOr (BitVec w))
    | none => .error s!"{shown s} is not a value of type {tyText (.int w)}"
  | .float e m, "poison" => pure (.poison : PoisonOr (BitVec (Core.floatWidth e m)))
  | .float e m, s => match floatConstOf e m s with
    | some v => pure (.value v : PoisonOr (BitVec (Core.floatWidth e m)))
    | none => .error s!"{shown s} is not a value of type {tyText (.float e m)}"
  | .ptr _, "poison" => pure (.poison : PoisonOr Memory.Pointer)
  | .ptr n, s => .error s!"{shown s} is not a value of type {tyText (.ptr n)}"

/-- One argument for each type of `ts`. It reads them in a loop of tail
calls, with the values read so far in `acc`, the last first, so it takes no
stack per argument (#405). -/
def readArgs (ts : List Core.Ty) (as : List String) : Except String (HVector toType ts) :=
  go ts as [] rfl
where
  go : (rest : List Core.Ty) → List String → (acc : List ((t : Core.Ty) × ⟦t⟧)) →
      (acc.map (·.1)).reverse ++ rest = ts → Except String (HVector toType ts)
    | [], [], acc, h => pure (ofRev acc (by simpa using h))
    | t :: rest, a :: as, acc, h => match readArg t a with
      | .ok v => go rest as (⟨t, v⟩ :: acc) (by simpa using h)
      | .error why => .error why
    | rest, as, _, _ => .error s!"{as.length} arguments are given for {rest.length} parameters"

/-- One argument for each type of `ts`, types of the sum of the core and
`gpu`, which are the core's, read as `readArgs` reads them. -/
def readGpuArgs (ts : List CoreGpu.Ty) (as : List String) : Except String (HVector toType ts) :=
  go ts as [] rfl
where
  go : (rest : List CoreGpu.Ty) → List String → (acc : List ((t : CoreGpu.Ty) × ⟦t⟧)) →
      (acc.map (·.1)).reverse ++ rest = ts → Except String (HVector toType ts)
    | [], [], acc, h => pure (ofRev acc (by simpa using h))
    | .inl t :: rest, a :: as, acc, h => match readArg t a with
      | .ok v => go rest as (⟨.inl t, v⟩ :: acc)
        (by rw [← h, List.map_cons, List.reverse_cons, List.append_assoc]; rfl)
      | .error why => .error why
    | .inr e :: _, _ :: _, _, _ => e.elim
    | rest, as, _, _ => .error s!"{as.length} arguments are given for {rest.length} parameters"

/-! # Scripted worlds -/

/-- One answer of a scripted world, the answer to one event: its results,
each spelled as `fir-ref run` spells a value, and the world's actions on
escaped memory, in order. -/
structure WorldAnswer where
  results : List String
  acts : List WorldAct
  deriving DecidableEq, Repr

/-- The words of a line, between spaces, tabs and a carriage return, so that
a script with CRLF line ends reads as one with LF. -/
def words (l : String) : List String :=
  ((l.map fun c => if c == '\t' || c == '\r' then ' ' else c).splitOn " ").filter (!·.isEmpty)

/-- A number spelled in ASCII decimal digits. -/
def natWord (w : String) : Option Nat := if w.all Char.isDigit then w.toNat? else none

/-- An integer spelled in ASCII decimal digits, after a `-` when it is
negative. -/
def intWord (w : String) : Option Int :=
  if w.startsWith "-" then (natWord (w.drop 1).toString).map (- ·) else (natWord w).map Int.ofNat

/-- A unit that the world writes: `0x` and hexadecimal digits for its bits,
`poison`, or `frag(M,H,O,I)`, the fragment `I` of a pointer of the memory
numbered `M` into the escaped allocation of handle `H`, or `none`, at the
offset `O`. -/
def wunitWord (w : String) : Option WUnit :=
  if w == "poison" then some .poison
  else if w.startsWith "0x" then (hexBits w).map .bits
  else if w.startsWith "frag(" && w.endsWith ")" then
    match ((w.drop 5).dropEnd 1).toString.splitOn "," with
    | [m, h, o, i] => do
      let h' ← if h == "none" then some none else (natWord h).map some
      pure (.frag (← natWord m) h' (← intWord o) (← natWord i))
    | _ => none
  else none

/-- The units of a `store`, read in a loop of tail calls, so that a line of
many units takes no stack per unit. -/
def wunitWords : List String → List WUnit → Option (List WUnit)
  | [], acc => some acc.reverse
  | w :: ws, acc => match wunitWord w with
    | some u => wunitWords ws (u :: acc)
    | none => none

/-- The world's action that a line spells: `store H O U...`, `alloc M N K`
or `free H`. -/
def worldActWords : List String → Option WorldAct
  | "store" :: h :: o :: us => do
    pure (.store (← natWord h) (← natWord o) (← wunitWords us []))
  | ["alloc", m, n, k] => do pure (.alloc (← natWord m) (← natWord n) (← natWord k))
  | ["free", h] => do pure (.free (← natWord h))
  | _ => none

/-- The scripted world that a text spells, one line at a time: `answer`
then the results of the next event's answer, each spelled as a value;
then that answer's actions on escaped memory, one per line, in order. A
line that is blank, or whose first word starts with `#`, says nothing. It
reads the lines in a loop of tail calls, so it takes no stack per line. -/
def readWorld (text : String) : Except String (List WorldAnswer) :=
  go (text.splitOn "\n") 1 []
where
  go : List String → Nat → List WorldAnswer → Except String (List WorldAnswer)
    | [], _, acc => .ok (acc.reverse.map fun a => { a with acts := a.acts.reverse })
    | l :: ls, n, acc => match words l, acc with
      | [], _ => go ls (n + 1) acc
      | w :: ws, acc =>
        if w.startsWith "#" then go ls (n + 1) acc
        else if w == "answer" then go ls (n + 1) (⟨ws, []⟩ :: acc)
        else match worldActWords (w :: ws), acc with
          | some act, a :: acc => go ls (n + 1) ({ a with acts := act :: a.acts } :: acc)
          | some _, [] => .error s!"line {n}: an action of the world comes before any answer"
          | none, _ => .error s!"line {n}: {shown l} is not an answer or an action of the world"

/-! # What `fir-ref run` reports on a file -/

/-- What `fir-ref run` reports on the bytes of `file`: it runs the function
that `func` names, a function of the module or a kernel of one of its
nested modules (`findFunc`), as the work-item `w`, on the arguments `args`,
with `fuel` steps, in the mode `mode`, and with the scripted world `world`
when it is given one. -/
def runBytes (file : String) (bytes : ByteArray) (fuel : Nat) (func : String)
    (args : List String) (mode : Mode := .scripted []) (w : Gpu.WorkItem := .single)
    (world : Option (List WorldAnswer) := none) : RunReport :=
  letI := w
  match parseBytes (d := CoreGpu) bytes with
  | .error e => { err := s!"{file}:{e.pos.line}:{e.pos.col}: parse error: {e.reason}", status := 1 }
  | .ok m =>
    let what := if file == "-" then "standard input" else shown file
    match findFunc m func with
    | none => { err := s!"fir-ref: {what} has no function {shown func}", status := 2 }
    | some (n, f) =>
      let ts := f.params.map (·.2)
      let name := func
      if ts.length ≠ args.length then
        { err := s!"fir-ref: {shown func} takes {arguments ts.length}, not {args.length}",
          status := 2 }
      else match readGpuArgs ts args, mode, world with
        | .error why, _, _ => { err := s!"fir-ref: {why}", status := 2 }
        | .ok vs, .scripted cs, none =>
          scriptedReport name (Gpu.scripted constOf n f vs fuel cs)
        | .ok vs, .exhaustive b, none =>
          exhaustiveReport name b (Gpu.exhaustive n f vs fuel b)
        | .ok vs, .exhaustiveNaN b nans, none =>
          exhaustiveNaNReport name b (Gpu.exhaustiveNaN n f vs fuel b nans)
        | .ok vs, .sampled s, none =>
          sampledReport name (Gpu.sampled draw n f vs fuel ⟨s.toUInt64⟩)
        | .ok _, _, some (a :: as) => worldMisfit name (a :: as).length
        | .ok vs, .scripted cs, some [] =>
          scriptedReportWith endFields name (Gpu.scriptedEnd constOf n f vs fuel cs)
        | .ok vs, .exhaustive b, some [] =>
          exhaustiveReportWith endFields name b (Gpu.exhaustiveEnd n f vs fuel b)
        | .ok vs, .exhaustiveNaN b nans, some [] =>
          exhaustiveNaNReportWith endFields name b (Gpu.exhaustiveNaNEnd n f vs fuel b nans)
        | .ok vs, .sampled s, some [] =>
          sampledReportWith endFields name (Gpu.sampledEnd draw n f vs fuel ⟨s.toUInt64⟩)

end FirRef
