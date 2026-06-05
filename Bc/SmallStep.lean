/-
  Fuel-bounded small-step operational semantics for the POSIX bc subset.

  This module defines a pure control-machine stepper. It shares the runtime data
  model and runtime helpers from `Bc.Runtime`; statements,
  function bodies, loops, and top-level items are stepped by local small-step
  transition rules.
-/

import Bc.Runtime

namespace Bc

namespace SmallStep

inductive Task where
  | topItems (items : Program)
  | topItem (item : TopItem)
  | stmts (stmts : List Stmt)
  | body (body : List BodyItem)
  | stmt (stmt : Stmt)
  | whileLoop (cond : Expr) (body : Stmt)
  | forCheck (cond update : Expr) (body : Stmt)
  | forAfterBody (cond update : Expr) (body : Stmt)
  deriving Repr

structure Config where
  state : RuntimeState
  tasks : List Task
  deriving Repr

inductive StepResult where
  | next (config : Config)
  | done (state : RuntimeState)
  | control (state : RuntimeState) (control : Control)
  | outOfFuel (state : RuntimeState)
  | runtimeError (state : RuntimeState) (message : String)
  deriving Repr

mutual

private def stmtContainsQuit : Stmt → Bool
  | .expr _ => false
  | .str _ => false
  | .auto _ => false
  | .if _ thenBranch => stmtContainsQuit thenBranch
  | .while _ body => stmtContainsQuit body
  | .for _ _ _ body => stmtContainsQuit body
  | .break => false
  | .return _ => false
  | .quit => true
  | .block body => bodyContainsQuit body

private def stmtsContainQuit : List Stmt → Bool
  | [] => false
  | stmt :: rest => stmtContainsQuit stmt || stmtsContainQuit rest

private def bodyItemContainsQuit : BodyItem → Bool
  | .stmts ss => stmtsContainQuit ss
  | .newline => false

private def bodyContainsQuit (body : List BodyItem) : Bool :=
  match body with
  | [] => false
  | item :: rest => bodyItemContainsQuit item || bodyContainsQuit rest

end

private def topItemContainsQuit : TopItem → Bool
  | .funDef defn => bodyContainsQuit defn.body
  | .stmts ss => stmtsContainQuit ss

private def next (st : RuntimeState) (tasks : List Task) : StepResult :=
  .next { state := st, tasks := tasks }

private def propagateBreak (st : RuntimeState) : List Task → StepResult
  | [] => .control st .break
  | .whileLoop _ _ :: rest => next st rest
  | .forAfterBody _ _ _ :: rest => next st rest
  | _ :: rest => propagateBreak st rest

private def propagateReturn (st : RuntimeState) (_value : Option Num) : List Task → StepResult
  | [] => .control st (.return _value)
  | _ :: rest => propagateReturn st _value rest

mutual

def evalExpr (fuel : Nat) (st : RuntimeState) (expr : Expr) : Result Num :=
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
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .assign lhs op rhs =>
          evalAssign fuel' st lhs op rhs
      | .rel first rest =>
          match evalExpr fuel' st first with
          | .ok st n => evalRelChain fuel' st n rest
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .bin op lhs rhs =>
          match evalExpr fuel' st lhs with
          | .ok st a =>
              match evalExpr fuel' st rhs with
              | .ok st b =>
                  let result? :=
                    match op with
                    | .add => Except.ok (Num.add a b)
                    | .sub => Except.ok (Num.sub a b)
                    | .mul => Except.ok (Num.mulWithScale a b st.scale)
                    | .div => Num.div? a b st.scale
                    | .mod => Num.modulo? a b st.scale
                    | .pow => Num.pow? a b st.scale
                  match result? with
                  | .ok n => .ok st n
                  | .error msg => .runtimeError st msg
              | .outOfFuel st => .outOfFuel st
              | .runtimeError st msg => .runtimeError st msg
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
    (rest : List (RelOp × Expr)) : Result Num :=
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
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg

def evalLValRef (fuel : Nat) (st : RuntimeState) (lv : LVal) :
    Result (Sum (Name ⊕ SpecialVar) (ArrayId × Nat)) :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match lv with
      | .var n => .ok st (Sum.inl (Sum.inl n))
      | .special v => .ok st (Sum.inl (Sum.inr v))
      | .array name idxExpr =>
          match evalExpr fuel' st idxExpr with
          | .ok st idxNum =>
              match indexOfNum? idxNum with
              | .ok idx =>
                  let (st, id) := ensureArrayId st name
                  .ok st (Sum.inr (id, idx))
              | .error msg => .runtimeError st msg
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg

def evalAssign (fuel : Nat) (st : RuntimeState) (lhs : LVal) (op : AssignOp) (rhs : Expr) :
    Result Num :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match evalLValRef fuel' st lhs with
      | .ok st ref =>
          match evalExpr fuel' st rhs with
          | .ok st rhsValue =>
              let old := readRef st ref
              let result? :=
                match op with
                | .assign => Except.ok rhsValue
                | .addAssign => Except.ok (Num.add old rhsValue)
                | .subAssign => Except.ok (Num.sub old rhsValue)
                | .mulAssign => Except.ok (Num.mulWithScale old rhsValue st.scale)
                | .divAssign => Num.div? old rhsValue st.scale
                | .modAssign => Num.modulo? old rhsValue st.scale
                | .powAssign => Num.pow? old rhsValue st.scale
              match result? with
              | .ok n => .ok (writeRef st ref n) n
              | .error msg => .runtimeError st msg
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .outOfFuel st => .outOfFuel st
      | .runtimeError st msg => .runtimeError st msg

def evalUnary (fuel : Nat) (st : RuntimeState) (op : UnOp) (arg : Expr) :
    Result Num :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match op with
      | .neg =>
          match evalExpr fuel' st arg with
          | .ok st n => .ok st (Num.neg n)
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .preIncr | .preDecr | .postIncr | .postDecr =>
          match lvalOfExpr? arg with
          | none => .runtimeError st "increment/decrement operand is not an lvalue"
          | some lv =>
              match evalLValRef fuel' st lv with
              | .ok st ref =>
                  let (st, old, newValue) := bumpRef st ref (op == .preIncr || op == .postIncr)
                  match op with
                  | .preIncr | .preDecr => .ok st newValue
                  | .postIncr | .postDecr => .ok st old
                  | .neg => .ok st newValue
              | .outOfFuel st => .outOfFuel st
              | .runtimeError st msg => .runtimeError st msg

def evalBuiltin (fuel : Nat) (st : RuntimeState) (fn : Builtin) (arg : Option Expr) :
    Result Num :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match fn, arg with
      | .length, some e =>
          match evalExpr fuel' st e with
          | .ok st n => .ok st (Num.ofInt (Int.ofNat n.length))
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .scale, some e =>
          match evalExpr fuel' st e with
          | .ok st n => .ok st (Num.ofInt (Int.ofNat n.scale))
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | .sqrt, some e =>
          match evalExpr fuel' st e with
          | .ok st n =>
              match Num.sqrt? n st.scale with
              | .ok r => .ok st r
              | .error msg => .runtimeError st msg
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg
      | _, _ => .runtimeError st "invalid builtin arity"

def evalArgValues (fuel : Nat) (st : RuntimeState) (args : List Arg) :
    Result (List (Sum Num Name)) :=
  match fuel with
  | 0 => .outOfFuel st
  | fuel' + 1 =>
      match args with
      | [] => .ok st []
      | arg :: rest =>
          let firstResult : Result (Sum Num Name) :=
            match arg with
            | .expr e =>
                match evalExpr fuel' st e with
                | .ok st n => Result.ok st (Sum.inl n)
                | .outOfFuel st => Result.outOfFuel st
                | .runtimeError st msg => Result.runtimeError st msg
            | .arrayRef name =>
                Result.ok st (Sum.inr name)
          match firstResult with
          | .ok st v =>
              match evalArgValues fuel' st rest with
              | .ok st vs => .ok st (v :: vs)
              | .outOfFuel st => .outOfFuel st
              | .runtimeError st msg => .runtimeError st msg
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg

def evalCall (fuel : Nat) (st : RuntimeState) (name : Name) (args : List Arg) :
    Result Num :=
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
                      Result.runtimeError { st with frames := st.frames.drop 1 }
                        "Break outside a loop"
                  | .ok st .stop => .ok { st with frames := st.frames.drop 1 } Num.zero
                  | .outOfFuel st => .outOfFuel { st with frames := st.frames.drop 1 }
                  | .runtimeError st msg => .runtimeError { st with frames := st.frames.drop 1 } msg
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg

private def stepExprStmt (fuel : Nat) (st : RuntimeState) (expr : Expr)
    (tasks : List Task) : StepResult :=
  match evalExpr fuel st expr with
  | .ok st n =>
      if isTopAssignment expr then
        next st tasks
      else
        next (printNumLine st n) tasks
  | .outOfFuel st => .outOfFuel st
  | .runtimeError st msg => .runtimeError st msg

private def stepStringStmt (st : RuntimeState) (s : String) (tasks : List Task) : StepResult :=
  next (appendOutput st (decodeBcString s)) tasks

private def stepCond (fuel : Nat) (st : RuntimeState) (cond : Expr)
    (onTrue : RuntimeState → List Task) (tasks : List Task) : StepResult :=
  match evalExpr fuel st cond with
  | .ok st n =>
      if n.isZero then
        next st tasks
      else
        next st (onTrue st ++ tasks)
  | .outOfFuel st => .outOfFuel st
  | .runtimeError st msg => .runtimeError st msg

def step (fuel : Nat) (config : Config) : StepResult :=
  match fuel with
  | 0 => .outOfFuel config.state
  | fuel' + 1 =>
      match config.tasks with
      | [] => .done config.state
      | task :: tasks =>
          match task with
          | .topItems [] => next config.state tasks
          | .topItems (item :: rest) =>
              if topItemContainsQuit item then
                .done { config.state with stopped := true }
              else
                next config.state (.topItem item :: .topItems rest :: tasks)
          | .topItem (.funDef defn) =>
              next (setFunction config.state defn) tasks
          | .topItem (.stmts ss) =>
              next config.state (.stmts ss :: tasks)
          | .stmts [] => next config.state tasks
          | .stmts (stmt :: rest) =>
              next config.state (.stmt stmt :: .stmts rest :: tasks)
          | .body [] => next config.state tasks
          | .body (.newline :: rest) =>
              next config.state (.body rest :: tasks)
          | .body (.stmts ss :: rest) =>
              next config.state (.stmts ss :: .body rest :: tasks)
          | .stmt (.expr e) => stepExprStmt fuel' config.state e tasks
          | .stmt (.str s) => stepStringStmt config.state s tasks
          | .stmt (.auto _) => next config.state tasks
          | .stmt (.if cond thenBranch) =>
              stepCond fuel' config.state cond (fun _ => [.stmt thenBranch]) tasks
          | .stmt (.while cond body) =>
              stepCond fuel' config.state cond (fun _ => [.stmt body, .whileLoop cond body]) tasks
          | .stmt (.for init cond update body) =>
              match evalExpr fuel' config.state init with
              | .ok st _ => next st (.forCheck cond update body :: tasks)
              | .outOfFuel st => .outOfFuel st
              | .runtimeError st msg => .runtimeError st msg
          | .stmt .break => propagateBreak config.state tasks
          | .stmt (.return value?) =>
              match value? with
              | none => propagateReturn config.state none tasks
              | some valueExpr =>
                  match evalExpr fuel' config.state valueExpr with
                  | .ok st value => propagateReturn st (some value) tasks
                  | .outOfFuel st => .outOfFuel st
                  | .runtimeError st msg => .runtimeError st msg
          | .stmt .quit =>
              .control { config.state with stopped := true } .stop
          | .stmt (.block body) =>
              next config.state (.body body :: tasks)
          | .whileLoop cond body =>
              stepCond fuel' config.state cond (fun _ => [.stmt body, .whileLoop cond body]) tasks
          | .forCheck cond update body =>
              stepCond fuel' config.state cond
                (fun _ => [.stmt body, .forAfterBody cond update body]) tasks
          | .forAfterBody cond update body =>
              match evalExpr fuel' config.state update with
              | .ok st _ => next st (.forCheck cond update body :: tasks)
              | .outOfFuel st => .outOfFuel st
              | .runtimeError st msg => .runtimeError st msg

private def runBodyConfig : Nat → Config → Result Control
  | 0, config => .outOfFuel config.state
  | fuel + 1, config =>
      match step (fuel + 1) config with
      | .next config => runBodyConfig fuel config
      | .done st => .ok st .normal
      | .control st control => .ok st control
      | .outOfFuel st => .outOfFuel st
      | .runtimeError st msg => .runtimeError st msg

def evalBody (fuel : Nat) (st : RuntimeState) (body : List BodyItem) : Result Control :=
  runBodyConfig fuel { state := st, tasks := [.body body] }

end

def initialConfig (st : RuntimeState) (program : Program) : Config :=
  { state := st, tasks := [.topItems program] }

def runConfig : Nat → Config → RunResult
  | 0, config => .outOfFuel config.state
  | fuel + 1, config =>
      match step (fuel + 1) config with
      | .next config => runConfig fuel config
      | .done st => .success st
      | .control st .normal => .success st
      | .control st .stop => .success st
      | .control st .break => .runtimeError st "Break outside a loop"
      | .control st (.return _) => .runtimeError st "Return outside of a function"
      | .outOfFuel st => .outOfFuel st
      | .runtimeError st msg => .runtimeError st msg

def runProgramWithState (fuel : Nat) (st : RuntimeState) (program : Program) : RunResult :=
  runConfig fuel (initialConfig st program)

def runProgram (fuel : Nat) (program : Program) : RunResult :=
  runProgramWithState fuel initialState program

end SmallStep

end Bc
