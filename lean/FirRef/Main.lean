import Fir
import FirRef.Utf8

/-!
`fir-ref`, the reference interpreter's executable (ADR-2026-10-29-2009). It
reads texts with the spec's parser and the core dialect, and prints them
with the spec's printer, `Module.print`. Its command line follows `funk`'s
(ADR-2026-10-30-1425).

fir has no nesting limit (#36), so `fir-ref` must give a verdict at any
depth. The spec's readers, decoder and printer recurse once per level, and
`fir-ref` runs them on the main thread that Lean's runtime gives a program,
so a text nested millions of levels deep overflows its stack. #47 gives
`fir-ref` implementations that take no stack per level, proved equal to the
spec's.
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

A FILE of - is standard input; -- ends the options.

Exit status: 0 when every FILE parses (and, with --check, is canonical), 1
when one does not parse or is not canonical, 2 on a usage or I/O error.
"

/-- The bytes of a file, or of standard input for `-`. -/
def readInput (file : String) : IO ByteArray :=
  if file == "-" then do (← IO.getStdin).readBinToEnd else IO.FS.readBinFile file

/-- What `fmt` reports on one file, and its exit status. -/
def fmtFile (check : Bool) (file : String) : IO UInt32 := do
  match ← (readInput file).toBaseIO with
  | .error e =>
    let why := ((toString e).splitOn "\n").headD ""
    let what := if file == "-" then "standard input" else file
    IO.eprintln s!"fir-ref: cannot read {what}: {why}"
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

/-- The arguments of `fmt`, as `funk` reads them: whether `--check` is
given, and the files. `--` ends the options. -/
def fmtArgs : Bool → List String → Except String (Bool × List String)
  | _, [] => .ok (false, [])
  | true, "--" :: rest => fmtArgs false rest
  | true, "--check" :: rest => do
    let (_, files) ← fmtArgs true rest
    pure (true, files)
  | options, a :: rest =>
    if options && a.startsWith "--" then .error s!"unknown option {a}"
    else do
      let (check, files) ← fmtArgs options rest
      pure (check, a :: files)

/-- Runs `fir-ref` on its arguments and returns its exit status. -/
def run (args : List String) : IO UInt32 := do
  let options := args.takeWhile (· != "--")
  if args.head? == some "help" || options.any (fun a => a == "-h" || a == "--help") then
    IO.print usage
    return 0
  let fail (why : String) : IO UInt32 := do
    IO.eprintln s!"fir-ref: {why}\n\n{usage}"
    return 2
  match args with
  | [] => fail "missing command"
  | "fmt" :: rest =>
    match fmtArgs true rest with
    | .error why => fail why
    | .ok (check, files) =>
      if files.isEmpty then fail "no FILE given; use - for standard input"
      else if (files.filter (· == "-")).length > 1 then
        fail "- may be given once: standard input can be read only once"
      else files.foldlM (fun status file => return max status (← fmtFile check file)) 0
  | cmd :: _ => fail s!"unknown command {cmd}"

end FirRef

/-- The entry point of `fir-ref`. -/
def main (args : List String) : IO UInt32 := FirRef.run args
