import FirRef.Run

/-!
The command line of `fir-ref run`
(`docs/decisions/fir-ref-command-line.md#fir-ref-run`):

`fir-ref run [--fuel N] [--choices C,C,... | --exhaustive [--choice-bits B] [--nans V,V,...]
| --seed S]
[--work-item-id X,Y,Z] [--work-group-id X,Y,Z] [--work-group-size X,Y,Z]
[--num-work-groups X,Y,Z] FILE @FUNC [ARG...]`

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
  quiet NaN of each sign and each `V` that is a NaN of its format
  (`Gpu.exhaustiveNaN`). Each `V` is a bit pattern, `0x` and hexadecimal
  digits, separated by commas, with no spaces; the empty text gives none.
* `--seed S`: sampled mode instead of scripted mode: each choice is drawn
  from a generator seeded with S, from 0 to 2^64 - 1.
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

/-- The options of `run` read so far. -/
structure RunOptions where
  fuel : Nat := defaultFuel
  choices : Option String := none
  exhaustive : Bool := false
  budget : Option Nat := none
  seed : Option Nat := none
  nans : Option (List Nat) := none
  workItem : Gpu.WorkItem := .single

/-- The number that the value `n` of the option `opt` spells: ASCII decimal
digits. -/
def optionNat (opt what n : String) : Except String Nat :=
  match if n.all Char.isDigit then n.toNat? else none with
  | some k => .ok k
  | none => .error s!"{opt} takes {what}, not {shown n}"

/-- The choices that `--choices` spells: none for the empty text, and
otherwise the texts between its commas. -/
def choiceList (s : String) : List String := if s.isEmpty then [] else s.splitOn ","

/-- The bit pattern that `v` spells: `0x` and one or more hexadecimal
digits. -/
def hexBits (v : String) : Option Nat :=
  let ds := v.toList.drop 2
  if v.startsWith "0x" && !ds.isEmpty then
    ds.foldlM (fun n c =>
      if c.isDigit then some (16 * n + (c.toNat - '0'.toNat))
      else if 'a' ≤ c && c ≤ 'f' then some (16 * n + (c.toNat - 'a'.toNat + 10))
      else if 'A' ≤ c && c ≤ 'F' then some (16 * n + (c.toNat - 'A'.toNat + 10))
      else none) 0
  else none

/-- The NaNs that `--nans` spells: none for the empty text, and otherwise
the bit pattern between each pair of commas. -/
def nanList (v : String) : Except String (List Nat) :=
  if v.isEmpty then .ok [] else match (v.splitOn ",").mapM hexBits with
    | some ns => .ok ns
    | none => .error s!"--nans takes bit patterns, as 0x7fc00000,0xffc00000, not {shown v}"

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
      | file :: func :: rest => .ok ⟨o.fuel, mode, file, func, rest, o.workItem⟩
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
          a == "--seed" || a == "--nans") then
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
            | _ => pure { o with choices := some v }
          go options o' pos rest'
        | [] => .error (match a with
          | "--fuel" => "--fuel takes a number of steps"
          | "--choice-bits" => "--choice-bits takes a number of bits"
          | "--seed" => "--seed takes a number below 2^64"
          | "--nans" => "--nans takes a list of bit patterns"
          | _ => "--choices takes a list of choices")
      else if options && a.startsWith "--" then .error s!"unknown option {shown a}"
      else go options o (a :: pos) rest

end FirRef
