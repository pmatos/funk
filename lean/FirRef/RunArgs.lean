import FirRef.Run

/-!
The command line of `fir-ref run` (ADR-2026-10-30-1856,
ADR-2026-10-30-2218, ADR-2026-10-31-0002):

`fir-ref run [--fuel N] [--choices C,C,... | --exhaustive [--choice-bits B] | --seed S] FILE @FUNC [ARG...]`

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
* `--seed S`: sampled mode instead of scripted mode: each choice is drawn
  from a generator seeded with S, from 0 to 2^64 - 1.

N, B and S are ASCII decimal digits. `--choices`, `--exhaustive` and
`--seed` go one at a time, and `--choice-bits` needs `--exhaustive`.
-/

namespace FirRef

/-- The arguments of `run`: its fuel, its mode, its file, the function and
the function's arguments. -/
structure RunArgs where
  fuel : Nat
  mode : Mode
  file : String
  func : String
  args : List String

/-- The options of `run` read so far. -/
structure RunOptions where
  fuel : Nat := defaultFuel
  choices : Option String := none
  exhaustive : Bool := false
  budget : Option Nat := none
  seed : Option Nat := none

/-- The number that the value `n` of the option `opt` spells: ASCII decimal
digits. -/
def optionNat (opt what n : String) : Except String Nat :=
  match if n.all Char.isDigit then n.toNat? else none with
  | some k => .ok k
  | none => .error s!"{opt} takes {what}, not {shown n}"

/-- The choices that `--choices` spells: none for the empty text, and
otherwise the texts between its commas. -/
def choiceList (s : String) : List String := if s.isEmpty then [] else s.splitOn ","

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
        | none, false, none, some s => .ok (.sampled s)
        | cs, false, none, none => .ok (.scripted (choiceList (cs.getD "")))
        | none, true, b, none => .ok (.exhaustive (b.getD defaultChoiceBits))
      match pos.reverse with
      | file :: func :: rest => .ok ⟨o.fuel, mode, file, func, rest⟩
      | [_] => .error "no @FUNC given"
      | [] => .error "no FILE given; use - for standard input"
    | a :: rest =>
      if options && a == "--" then go false o pos rest
      else if options && a == "--exhaustive" then go options { o with exhaustive := true } pos rest
      else if options && (a == "--fuel" || a == "--choices" || a == "--choice-bits" ||
          a == "--seed") then
        match rest with
        | v :: rest' => do
          let o' ← match a with
            | "--fuel" => do pure { o with fuel := ← optionNat a "a number of steps" v }
            | "--choice-bits" => do pure { o with budget := some (← optionNat a "a number of bits" v) }
            | "--seed" => do
              let s ← optionNat a "a number below 2^64" v
              if s < 2 ^ 64 then pure { o with seed := some s }
              else .error s!"--seed takes a number below 2^64, not {shown v}"
            | _ => pure { o with choices := some v }
          go options o' pos rest'
        | [] => .error (match a with
          | "--fuel" => "--fuel takes a number of steps"
          | "--choice-bits" => "--choice-bits takes a number of bits"
          | "--seed" => "--seed takes a number below 2^64"
          | _ => "--choices takes a list of choices")
      else if options && a.startsWith "--" then .error s!"unknown option {shown a}"
      else go options o (a :: pos) rest

end FirRef
