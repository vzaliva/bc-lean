/-
  Fuel-free structural small-step operational semantics for the POSIX bc subset.

  The one-step relation is over source-shaped residual syntax:

    RuntimeState × ProgramTerm --> RuntimeState × ProgramTerm

  `ProgramTerm`, `StmtTerm`, `ExprTerm`, and related terms mirror the source AST
  while adding the usual runtime terminals needed by a structural semantics:
  expression values, resolved lvalue targets, completed statements, and active
  function-call bodies. Fuel is used only by the executable runner.

  The declarative rule presentation and adequacy proofs are in `Bc/SmallStepRel.lean`
  and `Bc/SmallStepProperties.lean` respectively.
-/

import Bc.SmallStepShared

namespace Bc

namespace SmallStep

mutual

def stepExpr (st : RuntimeState) : ExprTerm → ExprOutcome
  | .value n => .value st n
  | .num raw => .next st (.value (Num.ofInputString raw (currentConstBase st)))
  | .var name => .next st (.value (lookupScalar st name))
  | .special v => .next st (.value (specialValue st v))
  | .arrayAccess name (.value indexValue) =>
      match indexOfNum? indexValue with
      | .ok idx =>
          let (st, id) := ensureArrayId st name
          .next st (.value (getArrayElem st id idx))
      | .error msg => .runtimeError st msg
  | .arrayAccess name index =>
      match stepExpr st index with
      | .next st index' => .next st (.arrayAccess name index')
      | .value st value => .next st (.arrayAccess name (.value value))
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .assign (.target target) op rhs =>
      .next st (.assignTarget target op rhs)
  | .assign lhs op rhs =>
      match stepLVal st lhs with
      | .next st lhs' => .next st (.assign lhs' op rhs)
      | .target st target => .next st (.assignTarget target op rhs)
      | .runtimeError st msg => .runtimeError st msg
  | .assignTarget target op (.value rhsValue) =>
      let old := readLValueTarget st target
      match applyAssign? op old rhsValue st.scale with
      | .ok result => .next (writeLValueTarget st target result) (.value result)
      | .error msg => .runtimeError st msg
  | .assignTarget target op rhs =>
      match stepExpr st rhs with
      | .next st rhs' => .next st (.assignTarget target op rhs')
      | .value st value => .next st (.assignTarget target op (.value value))
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .rel (.value left) [] =>
      .next st (.value left)
  | .rel (.value left) ((op, .value right) :: tail) =>
      let out := boolNum (applyRel op left right)
      match tail with
      | [] => .next st (.value out)
      | _ => .next st (.rel (.value out) tail)
  | .rel (.value left) ((op, rhs) :: tail) =>
      match stepExpr st rhs with
      | .next st rhs' => .next st (.rel (.value left) ((op, rhs') :: tail))
      | .value st value => .next st (.rel (.value left) ((op, .value value) :: tail))
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .rel first rest =>
      match stepExpr st first with
      | .next st first' => .next st (.rel first' rest)
      | .value st value => .next st (.rel (.value value) rest)
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .bin op (.value left) (.value right) =>
      match applyBin? op left right st.scale with
      | .ok result => .next st (.value result)
      | .error msg => .runtimeError st msg
  | .bin op (.value left) rhs =>
      match stepExpr st rhs with
      | .next st rhs' => .next st (.bin op (.value left) rhs')
      | .value st value => .next st (.bin op (.value left) (.value value))
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .bin op lhs rhs =>
      match stepExpr st lhs with
      | .next st lhs' => .next st (.bin op lhs' rhs)
      | .value st value => .next st (.bin op (.value value) rhs)
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .neg (.value value) =>
      .next st (.value (Num.neg value))
  | .neg arg =>
      match stepExpr st arg with
      | .next st arg' => .next st (.neg arg')
      | .value st value => .next st (.neg (.value value))
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .bump op (.target target) =>
      let (st, old, newValue) :=
        bumpLValueTarget st target (op == .preIncr || op == .postIncr)
      let value :=
        match op with
        | .preIncr | .preDecr => newValue
        | .postIncr | .postDecr => old
        | .neg => newValue
      .next st (.value value)
  | .bump op target =>
      match stepLVal st target with
      | .next st target' => .next st (.bump op target')
      | .target st target => .next st (.bump op (.target target))
      | .runtimeError st msg => .runtimeError st msg
  | .badBump _ _ =>
      .runtimeError st "increment/decrement operand is not an lvalue"
  | .call name args =>
      match lookupFunction st name with
      | none => .runtimeError st s!"Function {name} not defined"
      | some defn =>
          match stepArgs st args with
          | .next st args' => .next st (.call name args')
          | .values st argValues => enterFunction st defn argValues
          | .control st control => .control st control
          | .runtimeError st msg => .runtimeError st msg
  | .activeCall body =>
      match stepBody st body with
      | .next st body' => .next st (.activeCall body')
      | .done st => .next (popFrame st) (.value Num.zero)
      | .control st (.return value?) =>
          .next (popFrame st) (.value (returnValue value?))
      | .control st .break =>
          .runtimeError (popFrame st) "Break outside a loop"
      | .control st .normal =>
          .next (popFrame st) (.value Num.zero)
      | .control st .quit =>
          .control (popFrame st) .quit
      | .runtimeError st msg =>
          .runtimeError (popFrame st) msg
  | .builtin _ none =>
      .runtimeError st "invalid builtin arity"
  | .builtin fn (some (.value value)) =>
      match applyBuiltin? fn value st.scale with
      | .ok result => .next st (.value result)
      | .error msg => .runtimeError st msg
  | .builtin fn (some arg) =>
      match stepExpr st arg with
      | .next st arg' => .next st (.builtin fn (some arg'))
      | .value st value => .next st (.builtin fn (some (.value value)))
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .paren (.value value) =>
      .next st (.value value)
  | .paren body =>
      match stepExpr st body with
      | .next st body' => .next st (.paren body')
      | .value st value => .next st (.paren (.value value))
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg

def stepLVal (st : RuntimeState) : LValTerm → LValOutcome
  | .target target => .target st target
  | .var name => .next st (.target (.scalar name))
  | .special v => .next st (.target (.special v))
  | .array name (.value indexValue) =>
      match indexOfNum? indexValue with
      | .ok idx =>
          let (st, id) := ensureArrayId st name
          .next st (.target (.arrayElem id idx))
      | .error msg => .runtimeError st msg
  | .array name index =>
      match stepExpr st index with
      | .next st index' => .next st (.array name index')
      | .value st value => .next st (.array name (.value value))
      | .control st _ => .runtimeError st "control escaped from lvalue evaluation"
      | .runtimeError st msg => .runtimeError st msg

def stepArgs (st : RuntimeState) : List ArgTerm → ArgListOutcome
  | [] => .values st []
  | .arrayRef name :: rest =>
      match stepArgs st rest with
      | .next st rest' => .next st (.arrayRef name :: rest')
      | .values st values => .values st (.inr name :: values)
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .expr (.value value) :: rest =>
      match stepArgs st rest with
      | .next st rest' => .next st (.expr (.value value) :: rest')
      | .values st values => .values st (.inl value :: values)
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .expr expr :: rest =>
      match stepExpr st expr with
      | .next st expr' => .next st (.expr expr' :: rest)
      | .value st value => .next st (.expr (.value value) :: rest)
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg

def stepStmt (st : RuntimeState) : StmtTerm → StmtOutcome
  | .done => .done st
  | .expr original (.value value) =>
      if isTopAssignment original then
        .done st
      else
        .done (printNumLine st value)
  | .expr original expr =>
      match stepExpr st expr with
      | .next st expr' => .next st (.expr original expr')
      | .value st value => .next st (.expr original (.value value))
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .eval (.value _) =>
      .done st
  | .eval expr =>
      match stepExpr st expr with
      | .next st expr' => .next st (.eval expr')
      | .value st value => .next st (.eval (.value value))
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .str s =>
      .done (appendOutput st (decodeBcString s))
  | .auto _ =>
      .done st
  | .ifThen (.value cond) thenBranch =>
      if cond.isZero then .done st else .next st thenBranch
  | .ifThen cond thenBranch =>
      match stepExpr st cond with
      | .next st cond' => .next st (.ifThen cond' thenBranch)
      | .value st value => .next st (.ifThen (.value value) thenBranch)
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .while condSource (.value cond) body =>
      if cond.isZero then
        .done st
      else
        .next st (.loopBody body (.while condSource (ExprTerm.ofExpr condSource) body))
  | .while condSource cond body =>
      match stepExpr st cond with
      | .next st cond' => .next st (.while condSource cond' body)
      | .value st value => .next st (.while condSource (.value value) body)
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .forCheck condSource (.value cond) updateSource body =>
      if cond.isZero then
        .done st
      else
        .next st (.loopBody body (.forUpdate condSource updateSource
          (ExprTerm.ofExpr updateSource) body))
  | .forCheck condSource cond updateSource body =>
      match stepExpr st cond with
      | .next st cond' => .next st (.forCheck condSource cond' updateSource body)
      | .value st value => .next st (.forCheck condSource (.value value) updateSource body)
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .forUpdate condSource updateSource (.value _) body =>
      .next st (.forCheck condSource (ExprTerm.ofExpr condSource) updateSource body)
  | .forUpdate condSource updateSource update body =>
      match stepExpr st update with
      | .next st update' => .next st (.forUpdate condSource updateSource update' body)
      | .value st value => .next st (.forUpdate condSource updateSource (.value value) body)
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .loopBody .done after =>
      .next st after
  | .loopBody body after =>
      match stepStmt st body with
      | .next st body' => .next st (.loopBody body' after)
      | .done st => .next st after
      | .control st .break => .done st
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .seq .done second =>
      .next st second
  | .seq first second =>
      match stepStmt st first with
      | .next st first' => .next st (.seq first' second)
      | .done st => .next st second
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .break =>
      .control st .break
  | .return none =>
      .control st (.return none)
  | .return (some (.value value)) =>
      .control st (.return (some value))
  | .return (some expr) =>
      match stepExpr st expr with
      | .next st expr' => .next st (.return (some expr'))
      | .value st value => .next st (.return (some (.value value)))
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg
  | .quit =>
      .control { st with stopped := true } .quit
  | .block body =>
      match stepBody st body with
      | .next st body' => .next st (.block body')
      | .done st => .done st
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg

def stepBody (st : RuntimeState) : BodyTerm → BodyOutcome
  | .stmts [] => .done st
  | .stmts (stmt :: rest) =>
      match stepStmt st stmt with
      | .next st stmt' => .next st (.stmts (stmt' :: rest))
      | .done st => .next st (.stmts rest)
      | .control st control => .control st control
      | .runtimeError st msg => .runtimeError st msg

end

private def TopItemTerm.ofTermStmts : List StmtTerm → List TopItemTerm
  | [] => []
  | s :: rest => TopItemTerm.stmt s :: TopItemTerm.ofTermStmts rest

def TopItemTerm.ofTopItem (item : TopItem) : List TopItemTerm :=
  match item with
  | .funDef defn => [.funDef defn]
  | .stmts ss =>
      if stmtsContainQuit ss then [.stmt .quit] else TopItemTerm.ofTermStmts (StmtTerm.ofStmts ss)

def ProgramTerm.ofProgram : Program → ProgramTerm
  | [] => []
  | item :: rest => TopItemTerm.ofTopItem item ++ ProgramTerm.ofProgram rest

def next (st : RuntimeState) (program : ProgramTerm) : StepResult :=
  .next { state := st, program := program }

def step (config : Config) : StepResult :=
  match config.program with
  | [] => .done config.state
  | item :: rest =>
      if TopItemTerm.containsQuit item then
        .done { config.state with stopped := true }
      else
        match item with
        | .funDef defn =>
            next (setFunction config.state defn) rest
        | .stmt stmt =>
            match stepStmt config.state stmt with
            | .next st stmt' => next st (.stmt stmt' :: rest)
            | .done st => next st rest
            | .control st control => .control st control
            | .runtimeError st msg => .runtimeError st msg

private def runBodyConfig : Nat → RuntimeState → BodyTerm → Result Control
  | 0, st, _ => .outOfFuel st
  | fuel + 1, st, body =>
      match stepBody st body with
      | .next st body' => runBodyConfig fuel st body'
      | .done st => .ok st .normal
      | .control st control => .ok st control
      | .runtimeError st msg => .runtimeError st msg

def evalBody (fuel : Nat) (st : RuntimeState) (body : List BodyItem) : Result Control :=
  runBodyConfig fuel st (BodyTerm.ofBody body)

def initialConfig (st : RuntimeState) (program : Program) : Config :=
  { state := st, program := ProgramTerm.ofProgram program }

def runConfig : Nat → Config → RunResult
  | 0, config => .outOfFuel config.state
  | fuel + 1, config =>
      match step config with
      | .next config => runConfig fuel config
      | .done st => .success st
      | .control st .normal => .success st
      | .control st .quit => .success st
      | .control st .break => .runtimeError st "Break outside a loop"
      | .control st (.return _) => .runtimeError st "Return outside of a function"
      | .runtimeError st msg => .runtimeError st msg

def runProgramWithState (fuel : Nat) (st : RuntimeState) (program : Program) : RunResult :=
  runConfig fuel (initialConfig st program)

def runProgram (fuel : Nat) (program : Program) : RunResult :=
  runProgramWithState fuel initialState program

end SmallStep

end Bc
