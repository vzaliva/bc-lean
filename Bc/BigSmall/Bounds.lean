/-
  Step-count bounds for big↔small simulation witnesses.
-/

import Bc.BigSmall.Bridge

namespace Bc

namespace BigSmall

open SmallStep

mutual

/-- Small-step transitions needed to finish `ExprTerm.ofExpr e`. -/
def exprSmallSteps : Expr → Nat
  | .num _ => 2
  | .var _ => 2
  | .special _ => 2
  | .arrayAccess _ idx => exprSmallSteps idx + 3
  | .assign lhs _ rhs => lvalSmallSteps lhs + exprSmallSteps rhs + 4
  | .rel first rest => exprSmallSteps first + relRestSmallSteps rest + 2
  | .bin _ lhs rhs => exprSmallSteps lhs + exprSmallSteps rhs + 3
  | .unary .neg arg => exprSmallSteps arg + 2
  | .unary _ arg =>
      match arg with
      | .var _ => 2
      | .special _ => 2
      | .arrayAccess _ idx => exprSmallSteps idx + 3
      | .paren body => exprSmallSteps body + 2
      | _ => 1
  | .call _ args => argsSmallSteps args + 1
  | .builtin _ none => 1
  | .builtin _ (some arg) => exprSmallSteps arg + 2
  | .paren body => exprSmallSteps body + 1
termination_by e => sizeOf e

def relRestSmallSteps : List (RelOp × Expr) → Nat
  | [] => 0
  | (_, rhs) :: tail => exprSmallSteps rhs + relRestSmallSteps tail + 2
termination_by rest => sizeOf rest

def lvalSmallSteps : LVal → Nat
  | .var _ => 2
  | .special _ => 2
  | .array _ idx => exprSmallSteps idx + 3
termination_by lv => sizeOf lv

def argsSmallSteps : List Arg → Nat
  | [] => 1
  | arg :: rest => argSmallSteps arg + argsSmallSteps rest
termination_by args => sizeOf args

def argSmallSteps : Arg → Nat
  | .expr e => exprSmallSteps e + 1
  | .arrayRef _ => 1
termination_by arg => sizeOf arg

end

mutual

def stmtSmallSteps (fuel : Nat) : Stmt → Nat
  | .expr e => exprSmallSteps e + 1
  | .str _ => 1
  | .auto _ => 1
  | .if cond thenBranch => exprSmallSteps cond + stmtSmallSteps fuel thenBranch + 1
  | .while cond body =>
      fuel * (exprSmallSteps cond + stmtSmallSteps fuel body + 2) + 1
  | .for init cond update body =>
      exprSmallSteps init +
        fuel * (exprSmallSteps cond + stmtSmallSteps fuel body + exprSmallSteps update + 2) + 1
  | .break => 1
  | .return none => 1
  | .return (some e) => exprSmallSteps e + 1
  | .quit => 1
  | .block body => bodySmallSteps fuel body + 1
termination_by stmt => sizeOf stmt

def stmtsSmallSteps (fuel : Nat) : List Stmt → Nat
  | [] => 1
  | stmt :: rest => stmtSmallSteps fuel stmt + stmtsSmallSteps fuel rest
termination_by stmts => sizeOf stmts

def bodySmallSteps (fuel : Nat) : List BodyItem → Nat
  | [] => 1
  | .newline :: rest => bodySmallSteps fuel rest
  | .stmts ss :: rest => stmtsSmallSteps fuel ss + bodySmallSteps fuel rest
termination_by body => sizeOf body

def topItemSmallSteps (fuel : Nat) : TopItem → Nat
  | .funDef _ => 1
  | .stmts ss => stmtsSmallSteps fuel ss + 1
termination_by item => sizeOf item

def programSmallSteps (fuel : Nat) : Program → Nat
  | [] => 1
  | item :: rest => topItemSmallSteps fuel item + programSmallSteps fuel rest + 1
termination_by program => sizeOf program

end

def runExprWitness (e : Expr) (fuel : Nat) : Nat :=
  fuel * (exprSmallSteps e + 1) + exprSmallSteps e

def runLValWitness (lv : LVal) (fuel : Nat) : Nat :=
  fuel * (lvalSmallSteps lv + 1) + lvalSmallSteps lv

def runArgsWitness (args : List Arg) (fuel : Nat) : Nat :=
  fuel * (argsSmallSteps args + 1) + argsSmallSteps args

def runStmtWitness (s : Stmt) (fuel : Nat) : Nat :=
  fuel * (stmtSmallSteps fuel s + 1) + stmtSmallSteps fuel s

def runBodyWitness (body : List BodyItem) (fuel : Nat) : Nat :=
  fuel * (bodySmallSteps fuel body + 1) + bodySmallSteps fuel body

def runProgramWitness (program : Program) (fuel : Nat) : Nat :=
  fuel * (programSmallSteps fuel program + 1) + programSmallSteps fuel program

def runCallWitness (_name : Name) (args : List Arg) (body : List BodyItem) (fuel : Nat) : Nat :=
  runArgsWitness args fuel + runBodyWitness body fuel + 10

end BigSmall

end Bc
