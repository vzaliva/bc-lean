import Bc.BigStep
import Bc.SmallStep

namespace Bc
namespace BigSmallTest

private def quitFunction : FunDef :=
  { name := "f", params := [], body := [.stmts [.quit]] }

private def stateWithQuitFunction : RuntimeState :=
  setFunction initialState quitFunction

private def quitCallProgram : Program :=
  [.stmts [.expr (.call "f" [])]]

private def successStoppedWithOutput (expected : String) : RunResult → Bool
  | .success st => st.stopped && st.output == expected
  | _ => false

#guard successStoppedWithOutput "" (runProgramWithState 20 stateWithQuitFunction quitCallProgram)
#guard successStoppedWithOutput "" (SmallStep.runProgramWithState 20 stateWithQuitFunction
  quitCallProgram)

private def stateWithQuitFunctionAndX : RuntimeState :=
  { stateWithQuitFunction with globals := [("x", Num.ofInt 7)] }

private def quitCallAssignmentProgram : Program :=
  [.stmts [.expr (.assign (.var "x") .assign (.call "f" []))]]

private def successStoppedWithXUnchanged : RunResult → Bool
  | .success st =>
      st.stopped
        && st.output == ""
        && (lookupScalar st "x").coeff == 7
        && (lookupScalar st "x").scale == 0
  | _ => false

#guard successStoppedWithXUnchanged
  (runProgramWithState 20 stateWithQuitFunctionAndX quitCallAssignmentProgram)
#guard successStoppedWithXUnchanged
  (SmallStep.runProgramWithState 20 stateWithQuitFunctionAndX quitCallAssignmentProgram)

end BigSmallTest
end Bc
