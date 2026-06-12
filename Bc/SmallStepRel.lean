/-
  Declarative inductive presentation of the small-step semantics.

  `Bc/SmallStep.lean` defines the executable one-step function `step` (and its
  per-level steppers `stepExpr`, `stepLVal`, `stepArgs`, `stepStmt`, `stepBody`).
  This module gives a *rule-based* relation `StepProg` (built from the mutual
  family `StepExpr`/`StepLVal`/`StepArgs`/`StepStmt`/`StepBody`). Soundness and
  completeness against the executable steppers are proved in
  `Bc/SmallStepProperties.lean`; `Bc/Progress.lean` builds earned progress results
  on top of those theorems.

  Design (approach (a) — "lift combinators"):
  * Each construct gets contraction rules (perform the redex) and a single
    congruence rule per hole; the four-way outcome wrapping that the executable
    does inline is captured once by a `lift…` combinator.
  * The "resolved" forms — `ExprTerm.value` and `LValTerm.target` — are normal
    forms with *no* stepping rule, which makes the congruence rules unambiguous
    without guards (their premises are unsatisfiable on a resolved subterm). The
    only guards needed are `≠ .done` on the `seq`/`loopBody` congruences, because
    a completed statement is still consumed at the body/program level.
-/

import Bc.SmallStepShared

namespace Bc

namespace SmallStep


/-! ### Lift combinators

These mirror, once each, the four-way `match … with .next/.value/.control/…`
wrapping that the executable steppers perform inline at every congruence site. -/

/-- Lift a sub-expression outcome through a one-hole expression context whose
    resolved (value) case re-injects the value into the same hole. -/
def liftE (k : ExprTerm → ExprTerm) : ExprOutcome → ExprOutcome
  | .next st e => .next st (k e)
  | .value st v => .next st (k (.value v))
  | .control st c => .control st c
  | .runtimeError st m => .runtimeError st m

/-- Lift an lvalue outcome into an expression outcome (assign / bump). -/
def liftLE (kn : LValTerm → ExprTerm) (kt : RuntimeState → LValueTarget → ExprOutcome) :
    LValOutcome → ExprOutcome
  | .next st lv => .next st (kn lv)
  | .target st t => kt st t
  | .runtimeError st m => .runtimeError st m

/-- Lift an argument-list outcome into an expression outcome (call). -/
def liftAE (kn : List ArgTerm → ExprTerm)
    (kv : RuntimeState → List (Sum Num Name) → ExprOutcome) :
    ArgListOutcome → ExprOutcome
  | .next st a => .next st (kn a)
  | .values st vs => kv st vs
  | .control st c => .control st c
  | .runtimeError st m => .runtimeError st m

/-- Lift an active-call body outcome into an expression outcome (pops the frame). -/
def liftActiveCall : BodyOutcome → ExprOutcome
  | .next st body' => .next st (.activeCall body')
  | .done st => .next (popFrame st) (.value Num.zero)
  | .control st (.return value?) => .next (popFrame st) (.value (returnValue value?))
  | .control st .break => .runtimeError (popFrame st) "Break outside a loop"
  | .control st .normal => .next (popFrame st) (.value Num.zero)
  | .control st .quit => .control (popFrame st) .quit
  | .runtimeError st m => .runtimeError (popFrame st) m

/-- Lift the stepped index of an array lvalue. -/
def liftIndexLVal (name : Name) : ExprOutcome → LValOutcome
  | .next st e => .next st (.array name e)
  | .value st v => .next st (.array name (.value v))
  | .control st _ => .runtimeError st "control escaped from lvalue evaluation"
  | .runtimeError st m => .runtimeError st m

/-- Lift the recursive argument-list outcome (stepping the tail). -/
def liftArgsTail (kn : List ArgTerm → List ArgTerm)
    (kv : List (Sum Num Name) → List (Sum Num Name)) : ArgListOutcome → ArgListOutcome
  | .next st a => .next st (kn a)
  | .values st vs => .values st (kv vs)
  | .control st c => .control st c
  | .runtimeError st m => .runtimeError st m

/-- Lift a stepped head expression into an argument-list outcome. -/
def liftExprArgs (kn : ExprTerm → List ArgTerm) : ExprOutcome → ArgListOutcome
  | .next st e => .next st (kn e)
  | .value st v => .next st (kn (.value v))
  | .control st c => .control st c
  | .runtimeError st m => .runtimeError st m

/-- Lift a stepped sub-expression into a statement outcome. -/
def liftExprStmt (k : ExprTerm → StmtTerm) : ExprOutcome → StmtOutcome
  | .next st e => .next st (k e)
  | .value st v => .next st (k (.value v))
  | .control st c => .control st c
  | .runtimeError st m => .runtimeError st m

/-- Lift a stepped loop-body statement (a `break` exits the loop). -/
def liftLoopBody (after : StmtTerm) : StmtOutcome → StmtOutcome
  | .next st b => .next st (.loopBody b after)
  | .done st => .next st after
  | .control st .break => .done st
  | .control st c => .control st c
  | .runtimeError st m => .runtimeError st m

/-- Lift a stepped first statement of a sequence. -/
def liftSeq (second : StmtTerm) : StmtOutcome → StmtOutcome
  | .next st f => .next st (.seq f second)
  | .done st => .next st second
  | .control st c => .control st c
  | .runtimeError st m => .runtimeError st m

/-- Lift a stepped block body into a statement outcome. -/
def liftBlock : BodyOutcome → StmtOutcome
  | .next st b => .next st (.block b)
  | .done st => .done st
  | .control st c => .control st c
  | .runtimeError st m => .runtimeError st m

/-- Lift a stepped head statement into a body outcome. -/
def liftBodyStep (rest : List StmtTerm) : StmtOutcome → BodyOutcome
  | .next st s => .next st (.stmts (s :: rest))
  | .done st => .next st (.stmts rest)
  | .control st c => .control st c
  | .runtimeError st m => .runtimeError st m

/-- Lift a stepped top statement into a program step result. -/
def liftProg (rest : ProgramTerm) : StmtOutcome → StepResult
  | .next st s => .next { state := st, program := .stmt s :: rest }
  | .done st => .next { state := st, program := rest }
  | .control st c => .control st c
  | .runtimeError st m => .runtimeError st m

/-- The pure result of an in-place increment/decrement on a resolved target. -/
def bumpOutcome (op : UnOp) (st : RuntimeState) (target : LValueTarget) : ExprOutcome :=
  let (st, old, newValue) := bumpLValueTarget st target (op == .preIncr || op == .postIncr)
  let value :=
    match op with
    | .preIncr | .preDecr => newValue
    | .postIncr | .postDecr => old
    | .neg => newValue
  .next st (.value value)

/-! ### The declarative one-step relations -/

mutual

inductive StepExpr : RuntimeState → ExprTerm → ExprOutcome → Prop where
  | num {st raw} :
      StepExpr st (.num raw) (.next st (.value (Num.ofInputString raw (currentConstBase st))))
  | var {st name} :
      StepExpr st (.var name) (.next st (.value (lookupScalar st name)))
  | special {st v} :
      StepExpr st (.special v) (.next st (.value (specialValue st v)))
  | arrAccessOk {st st' name idxValue idx id} :
      indexOfNum? idxValue = .ok idx →
      ensureArrayId st name = (st', id) →
      StepExpr st (.arrayAccess name (.value idxValue)) (.next st' (.value (getArrayElem st' id idx)))
  | arrAccessErr {st name idxValue msg} :
      indexOfNum? idxValue = .error msg →
      StepExpr st (.arrayAccess name (.value idxValue)) (.runtimeError st msg)
  | arrAccessCongr {st name index o} :
      StepExpr st index o →
      StepExpr st (.arrayAccess name index) (liftE (fun e => .arrayAccess name e) o)
  | assignTarget0 {st target op rhs} :
      StepExpr st (.assign (.target target) op rhs) (.next st (.assignTarget target op rhs))
  | assignCongr {st lhs op rhs o} :
      StepLVal st lhs o →
      StepExpr st (.assign lhs op rhs)
        (liftLE (fun lv => .assign lv op rhs) (fun st t => .next st (.assignTarget t op rhs)) o)
  | assignTOk {st target op rhsValue result} :
      applyAssign? op (readLValueTarget st target) rhsValue st.scale = .ok result →
      StepExpr st (.assignTarget target op (.value rhsValue))
        (.next (writeLValueTarget st target result) (.value result))
  | assignTErr {st target op rhsValue msg} :
      applyAssign? op (readLValueTarget st target) rhsValue st.scale = .error msg →
      StepExpr st (.assignTarget target op (.value rhsValue)) (.runtimeError st msg)
  | assignTCongr {st target op rhs o} :
      StepExpr st rhs o →
      StepExpr st (.assignTarget target op rhs)
        (liftE (fun e => .assignTarget target op e) o)
  | relNil {st left} :
      StepExpr st (.rel (.value left) []) (.next st (.value left))
  | relDone {st left op right} :
      StepExpr st (.rel (.value left) ((op, .value right) :: []))
        (.next st (.value (boolNum (applyRel op left right))))
  | relCons {st left op right pair tail} :
      StepExpr st (.rel (.value left) ((op, .value right) :: pair :: tail))
        (.next st (.rel (.value (boolNum (applyRel op left right))) (pair :: tail)))
  | relRhsCongr {st left op rhs tail o} :
      StepExpr st rhs o →
      StepExpr st (.rel (.value left) ((op, rhs) :: tail))
        (liftE (fun e => .rel (.value left) ((op, e) :: tail)) o)
  | relFirstCongr {st first rest o} :
      StepExpr st first o →
      StepExpr st (.rel first rest) (liftE (fun e => .rel e rest) o)
  | binOk {st op left right result} :
      applyBin? op left right st.scale = .ok result →
      StepExpr st (.bin op (.value left) (.value right)) (.next st (.value result))
  | binErr {st op left right msg} :
      applyBin? op left right st.scale = .error msg →
      StepExpr st (.bin op (.value left) (.value right)) (.runtimeError st msg)
  | binRCongr {st op left rhs o} :
      StepExpr st rhs o →
      StepExpr st (.bin op (.value left) rhs) (liftE (fun e => .bin op (.value left) e) o)
  | binLCongr {st op lhs rhs o} :
      StepExpr st lhs o →
      StepExpr st (.bin op lhs rhs) (liftE (fun e => .bin op e rhs) o)
  | negVal {st value} :
      StepExpr st (.neg (.value value)) (.next st (.value (Num.neg value)))
  | negCongr {st arg o} :
      StepExpr st arg o →
      StepExpr st (.neg arg) (liftE (fun e => .neg e) o)
  | bumpTarget {st op target} :
      StepExpr st (.bump op (.target target)) (bumpOutcome op st target)
  | bumpCongr {st op target o} :
      StepLVal st target o →
      StepExpr st (.bump op target)
        (liftLE (fun lv => .bump op lv) (fun st t => .next st (.bump op (.target t))) o)
  | badBump {st op arg} :
      StepExpr st (.badBump op arg)
        (.runtimeError st "increment/decrement operand is not an lvalue")
  | callUndef {st name args} :
      lookupFunction st name = none →
      StepExpr st (.call name args) (.runtimeError st s!"Function {name} not defined")
  | callDef {st name args defn o} :
      lookupFunction st name = some defn →
      StepArgs st args o →
      StepExpr st (.call name args)
        (liftAE (fun a => .call name a) (fun st vs => enterFunction st defn vs) o)
  | activeCall {st body o} :
      StepBody st body o →
      StepExpr st (.activeCall body) (liftActiveCall o)
  | builtinNone {st fn} :
      StepExpr st (.builtin fn none) (.runtimeError st "invalid builtin arity")
  | builtinOk {st fn value result} :
      applyBuiltin? fn value st.scale = .ok result →
      StepExpr st (.builtin fn (some (.value value))) (.next st (.value result))
  | builtinErr {st fn value msg} :
      applyBuiltin? fn value st.scale = .error msg →
      StepExpr st (.builtin fn (some (.value value))) (.runtimeError st msg)
  | builtinCongr {st fn arg o} :
      StepExpr st arg o →
      StepExpr st (.builtin fn (some arg)) (liftE (fun e => .builtin fn (some e)) o)
  | parenVal {st value} :
      StepExpr st (.paren (.value value)) (.next st (.value value))
  | parenCongr {st body o} :
      StepExpr st body o →
      StepExpr st (.paren body) (liftE (fun e => .paren e) o)

inductive StepLVal : RuntimeState → LValTerm → LValOutcome → Prop where
  | var {st name} :
      StepLVal st (.var name) (.next st (.target (.scalar name)))
  | special {st v} :
      StepLVal st (.special v) (.next st (.target (.special v)))
  | arrOk {st st' name idxValue idx id} :
      indexOfNum? idxValue = .ok idx →
      ensureArrayId st name = (st', id) →
      StepLVal st (.array name (.value idxValue)) (.next st' (.target (.arrayElem id idx)))
  | arrErr {st name idxValue msg} :
      indexOfNum? idxValue = .error msg →
      StepLVal st (.array name (.value idxValue)) (.runtimeError st msg)
  | arrCongr {st name index o} :
      StepExpr st index o →
      StepLVal st (.array name index) (liftIndexLVal name o)

inductive StepArgs : RuntimeState → List ArgTerm → ArgListOutcome → Prop where
  | nil {st} :
      StepArgs st [] (.values st [])
  | arrayRef {st name rest o} :
      StepArgs st rest o →
      StepArgs st (.arrayRef name :: rest)
        (liftArgsTail (fun r => .arrayRef name :: r) (fun vs => .inr name :: vs) o)
  | exprVal {st value rest o} :
      StepArgs st rest o →
      StepArgs st (.expr (.value value) :: rest)
        (liftArgsTail (fun r => .expr (.value value) :: r) (fun vs => .inl value :: vs) o)
  | exprStep {st expr rest o} :
      StepExpr st expr o →
      StepArgs st (.expr expr :: rest) (liftExprArgs (fun e => .expr e :: rest) o)

inductive StepStmt : RuntimeState → StmtTerm → StmtOutcome → Prop where
  | done {st} :
      StepStmt st .done (.done st)
  | exprAssign {st original value} :
      isTopAssignment original = true →
      StepStmt st (.expr original (.value value)) (.done st)
  | exprPrint {st original value} :
      isTopAssignment original = false →
      StepStmt st (.expr original (.value value)) (.done (printNumLine st value))
  | exprCongr {st original expr o} :
      StepExpr st expr o →
      StepStmt st (.expr original expr) (liftExprStmt (fun e => .expr original e) o)
  | evalVal {st value} :
      StepStmt st (.eval (.value value)) (.done st)
  | evalCongr {st expr o} :
      StepExpr st expr o →
      StepStmt st (.eval expr) (liftExprStmt (fun e => .eval e) o)
  | str {st s} :
      StepStmt st (.str s) (.done (appendOutput st (decodeBcString s)))
  | auto {st params} :
      StepStmt st (.auto params) (.done st)
  | ifFalse {st cond thenBranch} :
      cond.isZero = true →
      StepStmt st (.ifThen (.value cond) thenBranch) (.done st)
  | ifTrue {st cond thenBranch} :
      cond.isZero = false →
      StepStmt st (.ifThen (.value cond) thenBranch) (.next st thenBranch)
  | ifCongr {st cond thenBranch o} :
      StepExpr st cond o →
      StepStmt st (.ifThen cond thenBranch) (liftExprStmt (fun e => .ifThen e thenBranch) o)
  | whileFalse {st condSource cond body} :
      cond.isZero = true →
      StepStmt st (.while condSource (.value cond) body) (.done st)
  | whileTrue {st condSource cond body} :
      cond.isZero = false →
      StepStmt st (.while condSource (.value cond) body)
        (.next st (.loopBody body (.while condSource (ExprTerm.ofExpr condSource) body)))
  | whileCongr {st condSource cond body o} :
      StepExpr st cond o →
      StepStmt st (.while condSource cond body)
        (liftExprStmt (fun e => .while condSource e body) o)
  | forFalse {st condSource cond updateSource body} :
      cond.isZero = true →
      StepStmt st (.forCheck condSource (.value cond) updateSource body) (.done st)
  | forTrue {st condSource cond updateSource body} :
      cond.isZero = false →
      StepStmt st (.forCheck condSource (.value cond) updateSource body)
        (.next st (.loopBody body
          (.forUpdate condSource updateSource (ExprTerm.ofExpr updateSource) body)))
  | forCongr {st condSource cond updateSource body o} :
      StepExpr st cond o →
      StepStmt st (.forCheck condSource cond updateSource body)
        (liftExprStmt (fun e => .forCheck condSource e updateSource body) o)
  | forUpdVal {st condSource updateSource value body} :
      StepStmt st (.forUpdate condSource updateSource (.value value) body)
        (.next st (.forCheck condSource (ExprTerm.ofExpr condSource) updateSource body))
  | forUpdCongr {st condSource updateSource update body o} :
      StepExpr st update o →
      StepStmt st (.forUpdate condSource updateSource update body)
        (liftExprStmt (fun e => .forUpdate condSource updateSource e body) o)
  | loopDone {st after} :
      StepStmt st (.loopBody .done after) (.next st after)
  | loopCongr {st body after o} :
      body ≠ .done →
      StepStmt st body o →
      StepStmt st (.loopBody body after) (liftLoopBody after o)
  | seqDone {st second} :
      StepStmt st (.seq .done second) (.next st second)
  | seqCongr {st first second o} :
      first ≠ .done →
      StepStmt st first o →
      StepStmt st (.seq first second) (liftSeq second o)
  | breakStmt {st} :
      StepStmt st .break (.control st .break)
  | retNone {st} :
      StepStmt st (.return none) (.control st (.return none))
  | retVal {st value} :
      StepStmt st (.return (some (.value value))) (.control st (.return (some value)))
  | retCongr {st expr o} :
      StepExpr st expr o →
      StepStmt st (.return (some expr)) (liftExprStmt (fun e => .return (some e)) o)
  | quitStmt {st} :
      StepStmt st .quit (.control { st with stopped := true } .quit)
  | block {st body o} :
      StepBody st body o →
      StepStmt st (.block body) (liftBlock o)

inductive StepBody : RuntimeState → BodyTerm → BodyOutcome → Prop where
  | nil {st} :
      StepBody st (.stmts []) (.done st)
  | cons {st stmt rest o} :
      StepStmt st stmt o →
      StepBody st (.stmts (stmt :: rest)) (liftBodyStep rest o)

end

/-- Top-level program one-step relation, mirroring `step`. -/
inductive StepProg : Config → StepResult → Prop where
  | nil {st} :
      StepProg ⟨st, []⟩ (.done st)
  | quitFunDef {st defn rest} :
      bodyContainsQuit defn.body = true →
      StepProg ⟨st, .funDef defn :: rest⟩ (.done { st with stopped := true })
  | funDef {st defn rest} :
      bodyContainsQuit defn.body = false →
      StepProg ⟨st, .funDef defn :: rest⟩ (.next ⟨setFunction st defn, rest⟩)
  | stmt {st stmt rest o} :
      StepStmt st stmt o →
      StepProg ⟨st, .stmt stmt :: rest⟩ (liftProg rest o)


end SmallStep

end Bc
