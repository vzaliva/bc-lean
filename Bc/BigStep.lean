/-
  Fuel-bounded big-step operational semantics for the POSIX bc subset.

  The evaluator is executable and models program output in RuntimeState.
  Recursive semantic functions are fuel-bounded and total; parser/pretty-printer
  infrastructure may remain partial, but this module does not use partial
  definitions.
-/

import Bc.Runtime

namespace Bc

/-- Big-step expression evaluation can escape with statement control when a
    called function executes `quit`. -/
inductive EvalResult (α : Type) where
  | ok (state : RuntimeState) (value : α)
  | control (state : RuntimeState) (control : Control)
  | outOfFuel (state : RuntimeState)
  | runtimeError (state : RuntimeState) (message : String)
  deriving Repr

mutual

def evalExpr (fuel : Nat) (st : RuntimeState) (expr : Expr) : EvalResult Num :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match expr with
      | .num raw =>
          .ok st (Num.ofInputString raw (currentConstBase st))
      | .var name =>
          .ok st (lookupScalar st name)
      | .special v =>
          .ok st (specialValue st v)
      | .arrayAccess name idxExpr =>
          match evalExpr fuel' st idxExpr with
          | .ok st idxNum =>
              match indexOfNum? idxNum with
              | .ok idx =>
                  let (st, id) := ensureArrayId st name
                  .ok st (getArrayElem st id idx)
              | .error msg => .runtimeError st msg
          | .control st control => .control st control
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .assign lhs op rhs =>
          evalAssign fuel' st lhs op rhs
      | .rel first rest =>
          match evalExpr fuel' st first with
          | .ok st n => evalRelChain fuel' st n rest
          | .control st control => .control st control
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .bin op lhs rhs =>
          match evalExpr fuel' st lhs with
          | .ok st a =>
              match evalExpr fuel' st rhs with
              | .ok st b =>
                  match applyBin? op a b st.scale with
                  | .ok n => .ok st n
                  | .error msg => .runtimeError st msg
              | .control st control => .control st control
              | .outOfFuel st => .outOfFuel st
              | .runtimeError st msg => .runtimeError st msg
          | .control st control => .control st control
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .unary op arg =>
          evalUnary fuel' st op arg
      | .call name args =>
          evalCall fuel' st name args
      | .builtin fn arg =>
          evalBuiltin fuel' st fn arg
      | .paren body =>
          evalExpr fuel' st body

def evalRelChain (fuel : Nat) (st : RuntimeState) (left : Num)
    (rest : List (RelOp × Expr)) : EvalResult Num :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match rest with
      | [] => .ok st left
      | (op, rhs) :: tail =>
          match evalExpr fuel' st rhs with
          | .ok st right =>
              let out := boolNum (applyRel op left right)
              if tail.isEmpty then
                .ok st out
              else
                evalRelChain fuel' st out tail
          | .control st control => .control st control
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg

def evalLValueTarget (fuel : Nat) (st : RuntimeState) (lv : LVal) :
    EvalResult LValueTarget :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match lv with
      | .var n => .ok st (.scalar n)
      | .special v => .ok st (.special v)
      | .array name idxExpr =>
          match evalExpr fuel' st idxExpr with
          | .ok st idxNum =>
              match indexOfNum? idxNum with
              | .ok idx =>
                  let (st, id) := ensureArrayId st name
                  .ok st (.arrayElem id idx)
              | .error msg => .runtimeError st msg
          | .control st _ => .runtimeError st "control escaped from lvalue evaluation"
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg

def evalAssign (fuel : Nat) (st : RuntimeState) (lhs : LVal) (op : AssignOp) (rhs : Expr) :
    EvalResult Num :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match evalLValueTarget fuel' st lhs with
      | .ok st target =>
          match evalExpr fuel' st rhs with
          | .ok st rhsValue =>
              let old := readLValueTarget st target
              match applyAssign? op old rhsValue st.scale with
              | .ok n => .ok (writeLValueTarget st target n) n
              | .error msg => .runtimeError st msg
          | .control st control => .control st control
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .control st control => .control st control
      | .outOfFuel st => .outOfFuel st
      | .runtimeError st msg => .runtimeError st msg

def evalUnary (fuel : Nat) (st : RuntimeState) (op : UnOp) (arg : Expr) :
    EvalResult Num :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match op with
      | .neg =>
          match evalExpr fuel' st arg with
          | .ok st n => .ok st (Num.neg n)
          | .control st control => .control st control
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .preIncr | .preDecr | .postIncr | .postDecr =>
          match lvalOfExpr? arg with
          | none => .runtimeError st "increment/decrement operand is not an lvalue"
          | some lv =>
              match evalLValueTarget fuel' st lv with
              | .ok st target =>
                  let (st, old, newValue) :=
                    bumpLValueTarget st target (op == .preIncr || op == .postIncr)
                  match op with
                  | .preIncr | .preDecr => .ok st newValue
                  | .postIncr | .postDecr => .ok st old
                  | .neg => .ok st newValue
              | .control st control => .control st control
              | .outOfFuel st => .outOfFuel st
              | .runtimeError st msg => .runtimeError st msg

def evalBuiltin (fuel : Nat) (st : RuntimeState) (fn : Builtin) (arg : Option Expr) :
    EvalResult Num :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match arg with
      | none => .runtimeError st "invalid builtin arity"
      | some e =>
          match evalExpr fuel' st e with
          | .ok st n =>
              match applyBuiltin? fn n st.scale with
              | .ok r => .ok st r
              | .error msg => .runtimeError st msg
          | .control st control => .control st control
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg

def evalArgValues (fuel : Nat) (st : RuntimeState) (args : List Arg) :
    EvalResult (List (Sum Num Name)) :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match args with
      | [] => .ok st []
      | arg :: rest =>
          let firstResult : EvalResult (Sum Num Name) :=
            match arg with
            | .expr e =>
                match evalExpr fuel' st e with
                | .ok st n => EvalResult.ok st (Sum.inl n)
                | .control st control => EvalResult.control st control
                | .outOfFuel st => EvalResult.outOfFuel st
                | .runtimeError st msg => EvalResult.runtimeError st msg
            | .arrayRef name =>
                EvalResult.ok st (Sum.inr name)
          match firstResult with
          | .ok st v =>
              match evalArgValues fuel' st rest with
              | .ok st vs => .ok st (v :: vs)
              | .control st control => .control st control
              | .outOfFuel st => .outOfFuel st
              | .runtimeError st msg => .runtimeError st msg
          | .control st control => .control st control
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg

def evalCall (fuel : Nat) (st : RuntimeState) (name : Name) (args : List Arg) :
    EvalResult Num :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match lookupFunction st name with
      | none => .runtimeError st s!"Function {name} not defined"
      | some defn =>
          match evalArgValues fuel' st args with
          | .ok st argValues =>
              let frame : Frame := { constBase := st.ibase }
              let stWithFrame := { st with frames := frame :: st.frames }
              match bindParams stWithFrame defn.params argValues with
              | .error msg => .runtimeError stWithFrame msg
              | .ok st =>
                  let st := bindAutoDecls st (collectAutos defn.body)
                  match evalBody fuel' st defn.body with
                  | .ok st .normal =>
                      .ok { st with frames := st.frames.drop 1 } Num.zero
                  | .ok st (.return v) =>
                      let value :=
                        match v with
                        | none => Num.zero
                        | some n => n
                      .ok { st with frames := st.frames.drop 1 } value
                  | .ok st .break =>
                      EvalResult.runtimeError { st with frames := st.frames.drop 1 }
                        "Break outside a loop"
                  | .ok st .quit => .control { st with frames := st.frames.drop 1 } .quit
                  | .outOfFuel st => .outOfFuel { st with frames := st.frames.drop 1 }
                  | .runtimeError st msg => .runtimeError { st with frames := st.frames.drop 1 } msg
          | .control st control => .control st control
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg

def evalStmt (fuel : Nat) (st : RuntimeState) (stmt : Stmt) : Result Control :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match stmt with
      | .expr e =>
          match evalExpr fuel' st e with
          | .ok st n =>
              if isTopAssignment e then .ok st .normal
              else .ok (printNumLine st n) .normal
          | .control st control => .ok st control
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .str s =>
          .ok (appendOutput st (decodeBcString s)) .normal
      | .auto _ =>
          .ok st .normal
      | .if cond thenBranch =>
          match evalExpr fuel' st cond with
          | .ok st n =>
              if n.isZero then .ok st .normal else evalStmt fuel' st thenBranch
          | .control st control => .ok st control
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .while cond body =>
          match evalExpr fuel' st cond with
          | .ok st n =>
              if n.isZero then
                .ok st .normal
              else
                match evalStmt fuel' st body with
                | .ok st .normal => evalStmt fuel' st stmt
                | .ok st .break => .ok st .normal
                | .ok st c => .ok st c
                | .outOfFuel st => .outOfFuel st
                | .runtimeError st msg => .runtimeError st msg
          | .control st control => .ok st control
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .for init cond update body =>
          match evalExpr fuel' st init with
          | .ok st _ => evalFor fuel' st cond update body
          | .control st control => .ok st control
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .break => .ok st .break
      | .return none => .ok st (.return none)
      | .return (some e) =>
          match evalExpr fuel' st e with
          | .ok st n => .ok st (.return (some n))
          | .control st control => .ok st control
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .quit => .ok { st with stopped := true } .quit
      | .block body =>
          evalBody fuel' st body

def evalFor (fuel : Nat) (st : RuntimeState) (cond update : Expr) (body : Stmt) :
    Result Control :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match evalExpr fuel' st cond with
      | .ok st n =>
          if n.isZero then
            .ok st .normal
          else
            match evalStmt fuel' st body with
            | .ok st .normal =>
                match evalExpr fuel' st update with
                | .ok st _ => evalFor fuel' st cond update body
                | .control st control => .ok st control
                | .outOfFuel st => .outOfFuel st
                | .runtimeError st msg => .runtimeError st msg
            | .ok st .break => .ok st .normal
            | .ok st c => .ok st c
            | .outOfFuel st => .outOfFuel st
            | .runtimeError st msg => .runtimeError st msg
      | .control st control => .ok st control
      | .outOfFuel st => .outOfFuel st
      | .runtimeError st msg => .runtimeError st msg

def evalStmts (fuel : Nat) (st : RuntimeState) (stmts : List Stmt) :
    Result Control :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match stmts with
      | [] => .ok st .normal
      | stmt :: rest =>
          match evalStmt fuel' st stmt with
          | .ok st .normal => evalStmts fuel' st rest
          | .ok st c => .ok st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg

def evalBody (fuel : Nat) (st : RuntimeState) (body : List BodyItem) :
    Result Control :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match body with
      | [] => .ok st .normal
      | .newline :: rest => evalBody fuel' st rest
      | .stmts ss :: rest =>
          match evalStmts fuel' st ss with
          | .ok st .normal => evalBody fuel' st rest
          | .ok st c => .ok st c
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg

end

def evalTopItem (fuel : Nat) (st : RuntimeState) : TopItem → Result Control
  | .funDef defn => .ok (setFunction st defn) .normal
  | .stmts ss => evalStmts fuel st ss

def evalProgramItems (fuel : Nat) (st : RuntimeState) (items : Program) :
    Result Control :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match items with
      | [] => .ok st .normal
      | item :: rest =>
          if TopItem.containsQuit item then
            .ok { st with stopped := true } .quit
          else
            match evalTopItem fuel' st item with
            | .ok st .normal =>
                if st.stopped then .ok st .quit else evalProgramItems fuel' st rest
            | .ok st .quit => .ok st .quit
            | .ok st .break => .runtimeError st "Break outside a loop"
            | .ok st (.return _) => .runtimeError st "Return outside of a function"
            | .outOfFuel st => .outOfFuel st
            | .runtimeError st msg => .runtimeError st msg

def runProgramWithState (fuel : Nat) (st : RuntimeState) (program : Program) : RunResult :=
  match evalProgramItems fuel st program with
  | .ok st _ => .success st
  | .outOfFuel st => .outOfFuel st
  | .runtimeError st msg => .runtimeError st msg

def runProgram (fuel : Nat) (program : Program) : RunResult :=
  runProgramWithState fuel initialState program

end Bc
