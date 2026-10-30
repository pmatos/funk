import Fir
import FirRef.Utf8

/-!
`fir-ref`, the reference interpreter's executable (ADR-2026-10-29-2009). It
reads texts with the spec's parser and the core dialect, and prints them
with the spec's printer, `Module.print`. It runs on the main thread that
Lean's runtime gives a program, whose stack is large, so deeply nested
texts parse and print as they do in `funk` (#36).
-/

namespace FirRef

open Fir

/-- The command line help. -/
def usage : String := "usage: fir-ref fmt [--check] FILE...

  fmt      Parse each FILE with the core dialect and print it in canonical
           form, as the spec's printer writes it. fmt does not validate: a
           module that parses has a canonical form.
             --check  print the name of each FILE that is not canonical
  -h, --help  Print this help.

Exit status: 0 when every FILE parses (and, with --check, is canonical), 1
when one does not parse or is not canonical, 2 on a usage or I/O error.
"

/-- What `fmt` reports on one file, and its exit status. -/
def fmtFile (check : Bool) (file : String) : IO UInt32 := do
  match ← (IO.FS.readBinFile file).toBaseIO with
  | .error e =>
    IO.eprintln s!"fir-ref: cannot read {file}: {e}"
    return 2
  | .ok bytes =>
    match parseBytes (d := CoreDialect) bytes with
    | .error e =>
      IO.eprintln s!"{file}:{e.pos.line}:{e.pos.col}: parse error: {e.reason}"
      return 1
    | .ok m =>
      let text := m.print
      if !check then
        IO.print text
        return 0
      else if text.toUTF8 == bytes then return 0
      else
        IO.println file
        return 1

/-- Runs `fir-ref` on its arguments and returns its exit status. -/
def run (args : List String) : IO UInt32 := do
  match args with
  | ["-h"] | ["--help"] =>
    IO.print usage
    return 0
  | [] =>
    IO.eprint usage
    return 2
  | "fmt" :: rest =>
    let check := rest.contains "--check"
    let files := rest.filter (· != "--check")
    if let some bad := files.find? (·.startsWith "--") then
      IO.eprintln s!"fir-ref: unknown option {bad}\n{usage}"
      return 2
    if files.isEmpty then
      IO.eprintln s!"fir-ref: no FILE given\n{usage}"
      return 2
    files.foldlM (fun status file => return max status (← fmtFile check file)) 0
  | cmd :: _ =>
    IO.eprintln s!"fir-ref: unknown command {cmd}\n{usage}"
    return 2

end FirRef

/-- The entry point of `fir-ref`. -/
def main (args : List String) : IO UInt32 := FirRef.run args
