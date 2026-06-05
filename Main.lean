import Bc.Basic
import Bc.Eval
import Bc.Parser

open Bc

structure CliOptions where
  fuel : Nat := 200000
  mathlib : Bool := false
  files : List String := []

private def usage : String :=
  "Usage: bc-lean [--fuel N] [-l|--mathlib] file..."

private def parseArgs : List String → CliOptions → Except String CliOptions
  | [], opts => .ok opts
  | "--fuel" :: n :: rest, opts =>
      match n.toNat? with
      | some fuel => parseArgs rest { opts with fuel := fuel }
      | none => .error s!"invalid --fuel value: {n}"
  | "--fuel" :: [], _ => .error "missing value for --fuel"
  | "-l" :: rest, opts | "--mathlib" :: rest, opts =>
      parseArgs rest { opts with mathlib := true }
  | "-h" :: _, _ | "--help" :: _, _ => .error usage
  | arg :: rest, opts =>
      if arg.startsWith "-" then
        .error s!"unknown option: {arg}"
      else
        parseArgs rest { opts with files := opts.files ++ [arg] }

private def loadProgram (path : String) : IO Program :=
  parseBcFile path

private def preloadMathlib (fuel : Nat) (st : RuntimeState) : IO RunResult := do
  let lib := "bc-1.07.1/bc/libmath.b"
  if ← System.FilePath.pathExists lib then
    let prog ← loadProgram lib
    return runProgramWithState fuel st prog
  else
    throw <| IO.userError s!"math library source not found: {lib}"

private def runFiles (opts : CliOptions) : IO UInt32 := do
  if opts.files.isEmpty then
    IO.eprintln usage
    return 1
  let mut st := initialState
  if opts.mathlib then
    match ← preloadMathlib opts.fuel st with
    | .success st' => st := st'
    | .outOfFuel st' =>
        IO.print st'.output
        IO.eprintln "bc-lean: out of fuel while loading math library"
        return 7
    | .runtimeError st' msg =>
        IO.print st'.output
        IO.eprintln s!"bc-lean: runtime error while loading math library: {msg}"
        return 6
  for file in opts.files do
    let prog ← loadProgram file
    match runProgramWithState opts.fuel st prog with
    | .success st' => st := st'
    | .outOfFuel st' =>
        IO.print st'.output
        IO.eprintln "bc-lean: out of fuel"
        return 7
    | .runtimeError st' msg =>
        IO.print st'.output
        IO.eprintln s!"bc-lean: runtime error: {msg}"
        return 6
  IO.print st.output
  return 0

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .ok opts => runFiles opts
  | .error msg =>
      IO.eprintln msg
      if msg == usage then return 0 else return 1
