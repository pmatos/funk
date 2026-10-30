import Fir
import FirRef.Utf8
import FirRef.Report

/-!
`fir-ref`, the reference interpreter's executable (ADR-2026-10-29-2009). It
reads texts with the spec's parser and the core dialect, and prints them
with the spec's printer, `Module.print`. Its command line follows `funk`'s
(ADR-2026-10-30-1425).

fir has no nesting limit (#36), so `fir-ref` must give a verdict at any
depth. It runs implementations of the spec's functions that take no stack
per level, each proved equal to its spec function and registered with
`@[csimp]` (ADR-2026-10-30-1450). The printer's and the decoder's are done:
`Module.print` runs as `FirRef.printModule`, in time linear in the text, and
`Fir.parse` as `FirRef.parse`, which decodes with `FirRef.decodeModule`. The
spec's readers still recurse once per level on the main thread that Lean's
runtime gives a program, so a text nested millions of levels deep overflows
its stack until the next stage of #47 replaces them too. `validate` runs the
spec's validation check, which walks nested blocks with `FirRef.allBlocks`
(ADR-2026-10-30-1742).
-/

namespace FirRef

open Fir

/-- The command line help. -/
def usage : String := "usage: fir-ref fmt [--check] FILE...
       fir-ref validate FILE...

  fmt       Parse each FILE with the core dialect and print it in canonical
            form, as the spec's printer writes it. fmt does not validate: a
            module that parses has a canonical form.
              --check  print the name of each FILE that is not canonical
  validate  Parse each FILE with the core dialect and run the spec's
            validation check. Print one JSON object per FILE, on one line,
            as funk verify --json does: the FILE, its verdict (accepted,
            parse-error, validation-error or io-error) and its diagnostics.
  -h, --help  Print this help.

A FILE of - is standard input; -- ends the options.

Exit status: 0 when every FILE parses (and, with fmt --check, is canonical,
or with validate, is valid), 1 when one does not parse, is not canonical or
is not valid, 2 on a usage or I/O error.
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

/-- What `validate` reports on one file, and its exit status. -/
def validateFile (file : String) : IO UInt32 := do
  match ← (readInput file).toBaseIO with
  | .error e =>
    let why := ((toString e).splitOn "\n").headD ""
    let what := if file == "-" then "standard input" else file
    IO.println (ioErrorReport file s!"cannot read {what}: {why}")
    return 2
  | .ok bytes =>
    let (line, status) := validateBytes file bytes
    IO.println line
    return status

/-- The files that `validate` is given. `--` ends the options, and it has
none. -/
def validateArgs : Bool → List String → Except String (List String)
  | _, [] => .ok []
  | true, "--" :: rest => validateArgs false rest
  | options, a :: rest =>
    if options && a.startsWith "--" then .error s!"unknown option {a}"
    else do pure (a :: (← validateArgs options rest))

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

/-- Runs `fir-ref` on its arguments and returns its exit status. Lean's
runtime decodes an argument that is not UTF-8 with U+FFFD in place of each
bad byte, so an argument that holds U+FFFD is refused, as `funk` refuses an
argument that is not UTF-8. A file whose name holds U+FFFD can still be
read as standard input, `-`. -/
def run (args : List String) : IO UInt32 := do
  let fail (why : String) : IO UInt32 := do
    IO.eprintln s!"fir-ref: {why}\n\n{usage}"
    return 2
  if let some bad := args.find? (·.contains '\uFFFD') then
    return ← fail s!"argument {bad.quote} is not UTF-8"
  let options := args.takeWhile (· != "--")
  if args.head? == some "help" || options.any (fun a => a == "-h" || a == "--help") then
    IO.print usage
    return 0
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
  | "validate" :: rest =>
    match validateArgs true rest with
    | .error why => fail why
    | .ok files =>
      if files.isEmpty then fail "no FILE given; use - for standard input"
      else if (files.filter (· == "-")).length > 1 then
        fail "- may be given once: standard input can be read only once"
      else files.foldlM (fun status file => return max status (← validateFile file)) 0
  | cmd :: _ => fail s!"unknown command {cmd}"

end FirRef

/-- The entry point of `fir-ref`. When it cannot write its output, it says so
on standard error if it can, and exits with 2, as `funk` does
(ADR-2026-10-30-1032); a reader that stopped reading, as `head` does, gets no
message. Read errors never reach here: each file's report carries them. -/
def main (args : List String) : IO UInt32 := do
  try
    let status ← FirRef.run args
    (← IO.getStdout).flush
    return status
  catch
    | .resourceVanished .. => return 2
    | e =>
      let why := ((toString e).splitOn "\n").headD ""
      try IO.eprintln s!"fir-ref: cannot write standard output: {why}" catch _ => pure ()
      return 2
