import Std.Data.HashSet
import Fir

/-!
What `fir-ref run` writes and reads that names no dialect
(`docs/decisions/fir-ref-command-line.md#fir-ref-run`): its defaults, its
report, the words of its messages, and how it finds the function that its
command line names, in the module or in a module nested in it.
-/

namespace FirRef

open Fir

/-- The default budget of `fir-ref run`: a million steps. -/
def defaultFuel : Nat := 1000000

/-- The default choice budget of exhaustive mode: 16 bits in all on one
path, so at most 65,536 paths. -/
def defaultChoiceBits : Nat := 16

/-- Text from the command line, with each control character shown as
`\xHH`, so that a message stays on one line. -/
def shown (s : String) : String :=
  s.foldl (fun out c =>
    if c.toNat < 0x20 || c.toNat == 0x7f then
      out ++ "\\x" ++ (if c.toNat < 0x10 then "0" else "") ++ Text.hex c.toNat
    else out.push c) ""

/-- `n` of a thing, in words: `1 argument`, `2 arguments`. -/
def count (n : Nat) (thing : String) : String := if n = 1 then s!"1 {thing}" else s!"{n} {thing}s"

/-- `n` arguments, in words. -/
def arguments (n : Nat) : String := count n "argument"

/-- What `fir-ref run` writes: its standard output and its standard error,
each one line or empty, and its exit status. -/
structure RunReport where
  out : String := ""
  err : String := ""
  status : UInt32
  deriving DecidableEq, Repr

/-- Each element once, in the order it first appears. -/
def distinct (xs : List String) : List String :=
  (xs.foldl (fun (seen, out) x => if seen.contains x then (seen, out) else (seen.insert x, out.push x))
    ((∅ : Std.HashSet String), (#[] : Array String))).2.toList

variable {d : Dialect}

/-- The function that `func` names in the module `M`, with the module it
runs in: `@f`, a function of `M`'s own table, as text writes its symbol, or
`@m::REST`, the function that `REST` names in the module `@m` nested in
`M`, at any depth, which runs in the module of its table
(`Module.nest`). A symbol as text writes it holds `::` only between quotes,
so each name has one reading. The loop takes no stack per level. -/
def findFunc (M : Module d) (func : String) : Option (Module d × Func d) :=
  go M.table func.toSlice
where
  go (t : SymbolTable d) (rest : String.Slice) : Option (Module d × Func d) :=
    match t.funcs.find? (fun f => (Text.printSymbol f.name).toSlice == rest) with
    | some f => some (M.nest t, f)
    | none =>
      let inner := t.items.findSome? fun
        | .module n ds is =>
          let head := Text.printSymbol n ++ "::"
          if rest.startsWith head then some ((⟨ds, is⟩ : SymbolTable d), rest.drop head.length)
          else none
        | _ => none
      match inner with
      | some (u, r) => if r.utf8ByteSize < rest.utf8ByteSize then go u r else none
      | none => none
  termination_by rest.utf8ByteSize

end FirRef
