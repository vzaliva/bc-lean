/-
  CLI entry point for AST parse golden tests.
-/

import Bc.Parser
import Bc.Pretty

open Bc

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.eprintln "usage: bc-parse-test FILE.b"
      return 1
  | path :: _ =>
      try
        let prog ← parseBcFile path
        IO.println (ppProgram prog)
        return 0
      catch e =>
        IO.eprintln (toString e)
        return 1
