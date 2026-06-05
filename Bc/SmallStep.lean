/-
  Fuel-free small-step operational semantics for the POSIX bc subset.

  This module defines a pure control-machine stepper. Fuel is used only by the
  executable runner to bound repeated stepping; the one-step transition itself
  is fuel-free. Expressions are stepped by the same task stack as statements,
  with continuations representing the remaining expression context.
-/

import Bc.Runtime

namespace Bc

namespace SmallStep

mutual

inductive ExprKont where
  | discard
  | printIfNeeded (original : Expr)
  | ifThen (thenBranch : Stmt)
  | whileCond (cond : Expr) (body : Stmt)
  | forInit (cond update : Expr) (body : Stmt)
  | forCond (cond update : Expr) (body : Stmt)
  | forUpdate (cond update : Expr) (body : Stmt)
  | returnValue
  | arrayAccess (name : Name) (k : ExprKont)
  | lvalArray (name : Name) (k : LValKont)
  | assignRhs (target : LValueTarget) (op : AssignOp) (k : ExprKont)
  | relRest (rest : List (RelOp × Expr)) (k : ExprKont)
  | relRhs (left : Num) (op : RelOp) (tail : List (RelOp × Expr)) (k : ExprKont)
  | binLeft (op : BinOp) (rhs : Expr) (k : ExprKont)
  | binRight (op : BinOp) (left : Num) (k : ExprKont)
  | neg (k : ExprKont)
  | builtin (fn : Builtin) (k : ExprKont)
  | callArg (defn : FunDef) (rest : List Arg) (rev : List (Sum Num Name)) (k : ExprKont)
  deriving Repr

inductive LValKont where
  | assign (op : AssignOp) (rhs : Expr) (k : ExprKont)
  | bump (op : UnOp) (k : ExprKont)
  deriving Repr

end

inductive Task where
  | topItems (items : Program)
  | topItem (item : TopItem)
  | stmts (stmts : List Stmt)
  | body (body : List BodyItem)
  | stmt (stmt : Stmt)
  | whileLoop (cond : Expr) (body : Stmt)
  | forCheck (cond update : Expr) (body : Stmt)
  | forAfterBody (cond update : Expr) (body : Stmt)
  | evalExpr (expr : Expr) (k : ExprKont)
  | exprValue (value : Num) (k : ExprKont)
  | evalLVal (lval : LVal) (k : LValKont)
  | lvalValue (target : LValueTarget) (k : LValKont)
  | callArgs (defn : FunDef) (args : List Arg) (rev : List (Sum Num Name)) (k : ExprKont)
  | functionReturn (k : ExprKont)
  deriving Repr

structure Config where
  state : RuntimeState
  tasks : List Task
  deriving Repr

inductive StepResult where
  | next (config : Config)
  | done (state : RuntimeState)
  | control (state : RuntimeState) (control : Control)
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

private def popFrame (st : RuntimeState) : RuntimeState :=
  { st with frames := st.frames.drop 1 }

private def returnValue : Option Num → Num
  | none => Num.zero
  | some n => n

private def applyBin? (op : BinOp) (a b : Num) (scale : Nat) : Except String Num :=
  match op with
  | .add => Except.ok (Num.add a b)
  | .sub => Except.ok (Num.sub a b)
  | .mul => Except.ok (Num.mulWithScale a b scale)
  | .div => Num.div? a b scale
  | .mod => Num.modulo? a b scale
  | .pow => Num.pow? a b scale

private def applyAssign? (op : AssignOp) (old rhs : Num) (scale : Nat) : Except String Num :=
  match op with
  | .assign => Except.ok rhs
  | .addAssign => Except.ok (Num.add old rhs)
  | .subAssign => Except.ok (Num.sub old rhs)
  | .mulAssign => Except.ok (Num.mulWithScale old rhs scale)
  | .divAssign => Num.div? old rhs scale
  | .modAssign => Num.modulo? old rhs scale
  | .powAssign => Num.pow? old rhs scale

private def enterFunction (st : RuntimeState) (defn : FunDef) (argValues : List (Sum Num Name))
    (k : ExprKont) (tasks : List Task) : StepResult :=
  let frame : Frame := { constBase := st.ibase }
  let stWithFrame := { st with frames := frame :: st.frames }
  match bindParams stWithFrame defn.params argValues with
  | .error msg => .runtimeError stWithFrame msg
  | .ok st =>
      let st := bindAutoDecls st (collectAutos defn.body)
      next st (.body defn.body :: .functionReturn k :: tasks)

private def propagateBreak (st : RuntimeState) : List Task → StepResult
  | [] => .control st .break
  | .whileLoop _ _ :: rest => next st rest
  | .forAfterBody _ _ _ :: rest => next st rest
  | .functionReturn _ :: _ => .runtimeError (popFrame st) "Break outside a loop"
  | _ :: rest => propagateBreak st rest

private def propagateReturn (st : RuntimeState) (value? : Option Num) : List Task → StepResult
  | [] => .control st (.return value?)
  | .functionReturn k :: rest => next (popFrame st) (.exprValue (returnValue value?) k :: rest)
  | _ :: rest => propagateReturn st value? rest

private def propagateStop (st : RuntimeState) : List Task → StepResult
  | [] => .control { st with stopped := true } .stop
  | .functionReturn _ :: rest => propagateStop (popFrame st) rest
  | _ :: rest => propagateStop st rest

def step (config : Config) : StepResult :=
  match config.tasks with
  | [] => .done config.state
  | task :: tasks =>
      let st := config.state
      match task with
      | .topItems [] => next st tasks
      | .topItems (item :: rest) =>
          if topItemContainsQuit item then
            .done { st with stopped := true }
          else
            next st (.topItem item :: .topItems rest :: tasks)
      | .topItem (.funDef defn) =>
          next (setFunction st defn) tasks
      | .topItem (.stmts ss) =>
          next st (.stmts ss :: tasks)
      | .stmts [] => next st tasks
      | .stmts (stmt :: rest) =>
          next st (.stmt stmt :: .stmts rest :: tasks)
      | .body [] => next st tasks
      | .body (.newline :: rest) =>
          next st (.body rest :: tasks)
      | .body (.stmts ss :: rest) =>
          next st (.stmts ss :: .body rest :: tasks)
      | .stmt (.expr e) =>
          next st (.evalExpr e (.printIfNeeded e) :: tasks)
      | .stmt (.str s) =>
          next (appendOutput st (decodeBcString s)) tasks
      | .stmt (.auto _) =>
          next st tasks
      | .stmt (.if cond thenBranch) =>
          next st (.evalExpr cond (.ifThen thenBranch) :: tasks)
      | .stmt (.while cond body) =>
          next st (.evalExpr cond (.whileCond cond body) :: tasks)
      | .stmt (.for init cond update body) =>
          next st (.evalExpr init (.forInit cond update body) :: tasks)
      | .stmt .break =>
          propagateBreak st tasks
      | .stmt (.return none) =>
          propagateReturn st none tasks
      | .stmt (.return (some valueExpr)) =>
          next st (.evalExpr valueExpr .returnValue :: tasks)
      | .stmt .quit =>
          propagateStop st tasks
      | .stmt (.block body) =>
          next st (.body body :: tasks)
      | .whileLoop cond body =>
          next st (.evalExpr cond (.whileCond cond body) :: tasks)
      | .forCheck cond update body =>
          next st (.evalExpr cond (.forCond cond update body) :: tasks)
      | .forAfterBody cond update body =>
          next st (.evalExpr update (.forUpdate cond update body) :: tasks)
      | .evalExpr (.num raw) k =>
          next st (.exprValue (Num.ofInputString raw (currentConstBase st)) k :: tasks)
      | .evalExpr (.var name) k =>
          next st (.exprValue (lookupScalar st name) k :: tasks)
      | .evalExpr (.special v) k =>
          next st (.exprValue (specialValue st v) k :: tasks)
      | .evalExpr (.arrayAccess name idxExpr) k =>
          next st (.evalExpr idxExpr (.arrayAccess name k) :: tasks)
      | .evalExpr (.assign lhs op rhs) k =>
          next st (.evalLVal lhs (.assign op rhs k) :: tasks)
      | .evalExpr (.rel first rest) k =>
          next st (.evalExpr first (.relRest rest k) :: tasks)
      | .evalExpr (.bin op lhs rhs) k =>
          next st (.evalExpr lhs (.binLeft op rhs k) :: tasks)
      | .evalExpr (.unary .neg arg) k =>
          next st (.evalExpr arg (.neg k) :: tasks)
      | .evalExpr (.unary op arg) k =>
          match lvalOfExpr? arg with
          | none => .runtimeError st "increment/decrement operand is not an lvalue"
          | some lv => next st (.evalLVal lv (.bump op k) :: tasks)
      | .evalExpr (.call name args) k =>
          match lookupFunction st name with
          | none => .runtimeError st s!"Function {name} not defined"
          | some defn => next st (.callArgs defn args [] k :: tasks)
      | .evalExpr (.builtin _ none) _ =>
          .runtimeError st "invalid builtin arity"
      | .evalExpr (.builtin fn (some arg)) k =>
          next st (.evalExpr arg (.builtin fn k) :: tasks)
      | .evalExpr (.paren body) k =>
          next st (.evalExpr body k :: tasks)
      | .exprValue _ .discard =>
          next st tasks
      | .exprValue value (.printIfNeeded original) =>
          if isTopAssignment original then
            next st tasks
          else
            next (printNumLine st value) tasks
      | .exprValue value (.ifThen thenBranch) =>
          if value.isZero then
            next st tasks
          else
            next st (.stmt thenBranch :: tasks)
      | .exprValue value (.whileCond cond body) =>
          if value.isZero then
            next st tasks
          else
            next st (.stmt body :: .whileLoop cond body :: tasks)
      | .exprValue _ (.forInit cond update body) =>
          next st (.forCheck cond update body :: tasks)
      | .exprValue value (.forCond cond update body) =>
          if value.isZero then
            next st tasks
          else
            next st (.stmt body :: .forAfterBody cond update body :: tasks)
      | .exprValue _ (.forUpdate cond update body) =>
          next st (.forCheck cond update body :: tasks)
      | .exprValue value .returnValue =>
          propagateReturn st (some value) tasks
      | .exprValue value (.arrayAccess name k) =>
          match indexOfNum? value with
          | .ok idx =>
              let (st, id) := ensureArrayId st name
              next st (.exprValue (getArrayElem st id idx) k :: tasks)
          | .error msg => .runtimeError st msg
      | .exprValue value (.lvalArray name k) =>
          match indexOfNum? value with
          | .ok idx =>
              let (st, id) := ensureArrayId st name
              next st (.lvalValue (.arrayElem id idx) k :: tasks)
          | .error msg => .runtimeError st msg
      | .exprValue value (.assignRhs target op k) =>
          let old := readLValueTarget st target
          match applyAssign? op old value st.scale with
          | .ok result =>
              next (writeLValueTarget st target result) (.exprValue result k :: tasks)
          | .error msg => .runtimeError st msg
      | .exprValue value (.relRest [] k) =>
          next st (.exprValue value k :: tasks)
      | .exprValue value (.relRest ((op, rhs) :: tail) k) =>
          next st (.evalExpr rhs (.relRhs value op tail k) :: tasks)
      | .exprValue right (.relRhs left op [] k) =>
          next st (.exprValue (boolNum (applyRel op left right)) k :: tasks)
      | .exprValue right (.relRhs left op (nextRel :: tail) k) =>
          let out := boolNum (applyRel op left right)
          next st (.exprValue out (.relRest (nextRel :: tail) k) :: tasks)
      | .exprValue value (.binLeft op rhs k) =>
          next st (.evalExpr rhs (.binRight op value k) :: tasks)
      | .exprValue right (.binRight op left k) =>
          match applyBin? op left right st.scale with
          | .ok result => next st (.exprValue result k :: tasks)
          | .error msg => .runtimeError st msg
      | .exprValue value (.neg k) =>
          next st (.exprValue (Num.neg value) k :: tasks)
      | .exprValue value (.builtin .length k) =>
          next st (.exprValue (Num.ofInt (Int.ofNat value.length)) k :: tasks)
      | .exprValue value (.builtin .scale k) =>
          next st (.exprValue (Num.ofInt (Int.ofNat value.scale)) k :: tasks)
      | .exprValue value (.builtin .sqrt k) =>
          match Num.sqrt? value st.scale with
          | .ok result => next st (.exprValue result k :: tasks)
          | .error msg => .runtimeError st msg
      | .exprValue value (.callArg defn rest rev k) =>
          next st (.callArgs defn rest (.inl value :: rev) k :: tasks)
      | .evalLVal (.var name) k =>
          next st (.lvalValue (.scalar name) k :: tasks)
      | .evalLVal (.special v) k =>
          next st (.lvalValue (.special v) k :: tasks)
      | .evalLVal (.array name idxExpr) k =>
          next st (.evalExpr idxExpr (.lvalArray name k) :: tasks)
      | .lvalValue target (.assign op rhs k) =>
          next st (.evalExpr rhs (.assignRhs target op k) :: tasks)
      | .lvalValue target (.bump op k) =>
          let (st, old, newValue) :=
            bumpLValueTarget st target (op == .preIncr || op == .postIncr)
          match op with
          | .preIncr | .preDecr =>
              next st (.exprValue newValue k :: tasks)
          | .postIncr | .postDecr =>
              next st (.exprValue old k :: tasks)
          | .neg =>
              next st (.exprValue newValue k :: tasks)
      | .callArgs defn [] rev k =>
          enterFunction st defn rev.reverse k tasks
      | .callArgs defn (.arrayRef name :: rest) rev k =>
          next st (.callArgs defn rest (.inr name :: rev) k :: tasks)
      | .callArgs defn (.expr e :: rest) rev k =>
          next st (.evalExpr e (.callArg defn rest rev k) :: tasks)
      | .functionReturn k =>
          next (popFrame st) (.exprValue Num.zero k :: tasks)

private def runBodyConfig : Nat → Config → Result Control
  | 0, config => .outOfFuel config.state
  | fuel + 1, config =>
      match step config with
      | .next config => runBodyConfig fuel config
      | .done st => .ok st .normal
      | .control st control => .ok st control
      | .runtimeError st msg => .runtimeError st msg

def evalBody (fuel : Nat) (st : RuntimeState) (body : List BodyItem) : Result Control :=
  runBodyConfig fuel { state := st, tasks := [.body body] }

def initialConfig (st : RuntimeState) (program : Program) : Config :=
  { state := st, tasks := [.topItems program] }

def runConfig : Nat → Config → RunResult
  | 0, config => .outOfFuel config.state
  | fuel + 1, config =>
      match step config with
      | .next config => runConfig fuel config
      | .done st => .success st
      | .control st .normal => .success st
      | .control st .stop => .success st
      | .control st .break => .runtimeError st "Break outside a loop"
      | .control st (.return _) => .runtimeError st "Return outside of a function"
      | .runtimeError st msg => .runtimeError st msg

def runProgramWithState (fuel : Nat) (st : RuntimeState) (program : Program) : RunResult :=
  runConfig fuel (initialConfig st program)

def runProgram (fuel : Nat) (program : Program) : RunResult :=
  runProgramWithState fuel initialState program

end SmallStep

end Bc
