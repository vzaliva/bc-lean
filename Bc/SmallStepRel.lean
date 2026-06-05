/-
  Declarative inductive presentation of the small-step semantics.

  `Bc/SmallStep.lean` defines the executable one-step function `step` (and its
  per-level steppers `stepExpr`, `stepLVal`, `stepArgs`, `stepStmt`, `stepBody`).
  This module gives a *rule-based* relation `StepProg` (built from the mutual
  family `StepExpr`/`StepLVal`/`StepArgs`/`StepStmt`/`StepBody`) and proves it is
  exactly the graph of the executable function (`Bc/Progress.lean` builds the
  earned progress/normal-form results on top of it).

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

import Bc.SmallStep

namespace Bc

namespace SmallStep

/-! ### Resolved-form predicates -/

def ExprTerm.isValue : ExprTerm → Bool
  | .value _ => true
  | _ => false

def LValTerm.isTarget : LValTerm → Bool
  | .target _ => true
  | _ => false

def StmtTerm.isDone : StmtTerm → Bool
  | .done => true
  | _ => false

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
  | quit {st item rest} :
      TopItemTerm.containsQuit item = true →
      StepProg ⟨st, item :: rest⟩ (.done { st with stopped := true })
  | funDef {st defn rest} :
      TopItemTerm.containsQuit (.funDef defn) = false →
      StepProg ⟨st, .funDef defn :: rest⟩ (.next ⟨setFunction st defn, rest⟩)
  | stmt {st stmt rest o} :
      TopItemTerm.containsQuit (.stmt stmt) = false →
      StepStmt st stmt o →
      StepProg ⟨st, .stmt stmt :: rest⟩ (liftProg rest o)

/-! ### Inversion: resolved forms are normal forms -/

theorem StepExpr.not_value {st v o} : ¬ StepExpr st (.value v) o := by
  intro h; cases h

theorem StepLVal.not_target {st t o} : ¬ StepLVal st (.target t) o := by
  intro h; cases h

theorem StepExpr.not_isValue {st index o} (h : StepExpr st index o) :
    ExprTerm.isValue index = false := by
  cases index <;> first | rfl | exact absurd h StepExpr.not_value

theorem StepLVal.not_isTarget {st target o} (h : StepLVal st target o) :
    LValTerm.isTarget target = false := by
  cases target <;> first | rfl | exact absurd h StepLVal.not_target

/-- Reduction lemma for expression congruences: a non-value subterm makes the
    executable take the matching expression-context branch. -/
theorem stepExpr_arrayAccess_eq {st name index} (h : ExprTerm.isValue index = false) :
    stepExpr st (.arrayAccess name index) =
      liftE (fun e => .arrayAccess name e) (stepExpr st index) := by
  cases index <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepExpr_assignTarget_eq {st target op rhs} (h : ExprTerm.isValue rhs = false) :
    stepExpr st (.assignTarget target op rhs) =
      liftE (fun e => .assignTarget target op e) (stepExpr st rhs) := by
  cases rhs <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepExpr_relRhs_eq {st left op rhs tail} (h : ExprTerm.isValue rhs = false) :
    stepExpr st (.rel (.value left) ((op, rhs) :: tail)) =
      liftE (fun e => .rel (.value left) ((op, e) :: tail)) (stepExpr st rhs) := by
  cases rhs <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepExpr_relFirst_eq {st first rest} (h : ExprTerm.isValue first = false) :
    stepExpr st (.rel first rest) = liftE (fun e => .rel e rest) (stepExpr st first) := by
  cases first <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepExpr_binR_eq {st op left rhs} (h : ExprTerm.isValue rhs = false) :
    stepExpr st (.bin op (.value left) rhs) =
      liftE (fun e => .bin op (.value left) e) (stepExpr st rhs) := by
  cases rhs <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepExpr_binL_eq {st op lhs rhs} (h : ExprTerm.isValue lhs = false) :
    stepExpr st (.bin op lhs rhs) = liftE (fun e => .bin op e rhs) (stepExpr st lhs) := by
  cases lhs <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepExpr_neg_eq {st arg} (h : ExprTerm.isValue arg = false) :
    stepExpr st (.neg arg) = liftE (fun e => .neg e) (stepExpr st arg) := by
  cases arg <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepExpr_builtin_eq {st fn arg} (h : ExprTerm.isValue arg = false) :
    stepExpr st (.builtin fn (some arg)) =
      liftE (fun e => .builtin fn (some e)) (stepExpr st arg) := by
  cases arg <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepExpr_paren_eq {st body} (h : ExprTerm.isValue body = false) :
    stepExpr st (.paren body) = liftE (fun e => .paren e) (stepExpr st body) := by
  cases body <;> first | rfl | simp_all [ExprTerm.isValue]

/-- Reduction lemma for expression contexts over lvalues: a non-target lvalue
    makes the executable take the matching lvalue-context branch. -/
theorem stepExpr_assign_eq {st lhs op rhs} (h : LValTerm.isTarget lhs = false) :
    stepExpr st (.assign lhs op rhs) =
      liftLE (fun lv => .assign lv op rhs) (fun st t => .next st (.assignTarget t op rhs))
        (stepLVal st lhs) := by
  cases lhs <;> first | rfl | simp_all [LValTerm.isTarget]

theorem stepExpr_bump_eq {st op target} (h : LValTerm.isTarget target = false) :
    stepExpr st (.bump op target) =
      liftLE (fun lv => .bump op lv) (fun st t => .next st (.bump op (.target t)))
        (stepLVal st target) := by
  cases target <;> first | rfl | simp_all [LValTerm.isTarget]

/-- Reduction lemma for the lvalue-array congruence: a non-value index makes the
    executable take the congruence branch, matching `liftIndexLVal`. -/
theorem stepLVal_array_eq {st name index} (h : ExprTerm.isValue index = false) :
    stepLVal st (.array name index) = liftIndexLVal name (stepExpr st index) := by
  cases index <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepArgs_expr_eq {st expr rest} (h : ExprTerm.isValue expr = false) :
    stepArgs st (.expr expr :: rest) =
      liftExprArgs (fun e => .expr e :: rest) (stepExpr st expr) := by
  cases expr <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepStmt_expr_eq {st original expr} (h : ExprTerm.isValue expr = false) :
    stepStmt st (.expr original expr) =
      liftExprStmt (fun e => .expr original e) (stepExpr st expr) := by
  cases expr <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepStmt_eval_eq {st expr} (h : ExprTerm.isValue expr = false) :
    stepStmt st (.eval expr) = liftExprStmt (fun e => .eval e) (stepExpr st expr) := by
  cases expr <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepStmt_ifThen_eq {st cond thenBranch} (h : ExprTerm.isValue cond = false) :
    stepStmt st (.ifThen cond thenBranch) =
      liftExprStmt (fun e => .ifThen e thenBranch) (stepExpr st cond) := by
  cases cond <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepStmt_while_eq {st condSource cond body} (h : ExprTerm.isValue cond = false) :
    stepStmt st (.while condSource cond body) =
      liftExprStmt (fun e => .while condSource e body) (stepExpr st cond) := by
  cases cond <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepStmt_forCheck_eq {st condSource cond updateSource body}
    (h : ExprTerm.isValue cond = false) :
    stepStmt st (.forCheck condSource cond updateSource body) =
      liftExprStmt (fun e => .forCheck condSource e updateSource body) (stepExpr st cond) := by
  cases cond <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepStmt_forUpdate_eq {st condSource updateSource update body}
    (h : ExprTerm.isValue update = false) :
    stepStmt st (.forUpdate condSource updateSource update body) =
      liftExprStmt (fun e => .forUpdate condSource updateSource e body)
        (stepExpr st update) := by
  cases update <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepStmt_return_eq {st expr} (h : ExprTerm.isValue expr = false) :
    stepStmt st (.return (some expr)) =
      liftExprStmt (fun e => .return (some e)) (stepExpr st expr) := by
  cases expr <;> first | rfl | simp_all [ExprTerm.isValue]

theorem stepStmt_loopBody_eq {st body after} (h : body ≠ .done) :
    stepStmt st (.loopBody body after) = liftLoopBody after (stepStmt st body) := by
  cases body <;> first | contradiction | rfl

theorem stepStmt_seq_eq {st first second} (h : first ≠ .done) :
    stepStmt st (.seq first second) = liftSeq second (stepStmt st first) := by
  cases first <;> first | contradiction | rfl

/-! ### Soundness: every derivable step is the one the executable takes -/

/-- Shared simp set: unfold every stepper and lift combinator. -/
local macro "ss" : tactic =>
  `(tactic| simp_all [stepExpr, stepLVal, stepArgs, stepStmt, stepBody,
      liftE, liftLE, liftAE, liftActiveCall, liftIndexLVal, liftArgsTail, liftExprArgs,
      liftExprStmt, liftLoopBody, liftSeq, liftBlock, liftBodyStep, bumpOutcome,
      StepExpr.not_isValue, StepLVal.not_isTarget, stepExpr_arrayAccess_eq,
      stepExpr_assign_eq, stepExpr_assignTarget_eq, stepExpr_relRhs_eq,
      stepExpr_relFirst_eq, stepExpr_binR_eq, stepExpr_binL_eq, stepExpr_neg_eq,
      stepExpr_bump_eq, stepExpr_builtin_eq, stepExpr_paren_eq, stepLVal_array_eq,
      stepArgs_expr_eq, stepStmt_expr_eq, stepStmt_eval_eq, stepStmt_ifThen_eq,
      stepStmt_while_eq, stepStmt_forCheck_eq, stepStmt_forUpdate_eq, stepStmt_return_eq])

local macro "sound_intro" : tactic =>
  `(tactic| all_goals (intros; first | assumption | (ss; done) | (ss; rfl) | rfl | skip))


theorem stepExpr_sound {st e o} (h : StepExpr st e o) : stepExpr st e = o := by
  apply @StepExpr.rec st
    (motive_1 := fun e o _ => stepExpr st e = o)
    (motive_2 := fun lv o _ => stepLVal st lv = o)
    (motive_3 := fun a o _ => stepArgs st a = o)
    (motive_4 := fun s o _ => stepStmt st s = o)
    (motive_5 := fun b o _ => stepBody st b = o)
  sound_intro
  case arrAccessCongr name index o hprem hih =>
    rw [stepExpr_arrayAccess_eq (StepExpr.not_isValue hprem), hih]
  case assignCongr lhs op rhs o hprem hih =>
    rw [stepExpr_assign_eq (StepLVal.not_isTarget hprem), hih]
  case assignTCongr target op rhs o hprem hih =>
    rw [stepExpr_assignTarget_eq (StepExpr.not_isValue hprem), hih]
  case relRhsCongr left op rhs tail o hprem hih =>
    rw [stepExpr_relRhs_eq (StepExpr.not_isValue hprem), hih]
  case relFirstCongr first rest o hprem hih =>
    rw [stepExpr_relFirst_eq (StepExpr.not_isValue hprem), hih]
  case binRCongr op left rhs o hprem hih =>
    rw [stepExpr_binR_eq (StepExpr.not_isValue hprem), hih]
  case binLCongr op lhs rhs o hprem hih =>
    rw [stepExpr_binL_eq (StepExpr.not_isValue hprem), hih]
  case negCongr arg o hprem hih =>
    rw [stepExpr_neg_eq (StepExpr.not_isValue hprem), hih]
  case bumpCongr op target o hprem hih =>
    rw [stepExpr_bump_eq (StepLVal.not_isTarget hprem), hih]
  case builtinCongr fn arg o hprem hih =>
    rw [stepExpr_builtin_eq (StepExpr.not_isValue hprem), hih]
  case parenCongr body o hprem hih =>
    rw [stepExpr_paren_eq (StepExpr.not_isValue hprem), hih]
  case arrCongr name index o hprem hih =>
    rw [stepLVal_array_eq (StepExpr.not_isValue hprem), hih]
  case exprStep expr rest o hprem hih =>
    rw [stepArgs_expr_eq (StepExpr.not_isValue hprem), hih]
  case exprCongr original expr o hprem hih =>
    rw [stepStmt_expr_eq (StepExpr.not_isValue hprem), hih]
  case evalCongr expr o hprem hih =>
    rw [stepStmt_eval_eq (StepExpr.not_isValue hprem), hih]
  case ifCongr cond thenBranch o hprem hih =>
    rw [stepStmt_ifThen_eq (StepExpr.not_isValue hprem), hih]
  case whileCongr condSource cond body o hprem hih =>
    rw [stepStmt_while_eq (StepExpr.not_isValue hprem), hih]
  case forCongr condSource cond updateSource body o hprem hih =>
    rw [stepStmt_forCheck_eq (StepExpr.not_isValue hprem), hih]
  case forUpdCongr condSource updateSource update body o hprem hih =>
    rw [stepStmt_forUpdate_eq (StepExpr.not_isValue hprem), hih]
  case retCongr expr o hprem hih =>
    rw [stepStmt_return_eq (StepExpr.not_isValue hprem), hih]

theorem stepLVal_sound {st lv o} (h : StepLVal st lv o) : stepLVal st lv = o := by
  apply @StepLVal.rec st
    (motive_1 := fun e o _ => stepExpr st e = o)
    (motive_2 := fun lv o _ => stepLVal st lv = o)
    (motive_3 := fun a o _ => stepArgs st a = o)
    (motive_4 := fun s o _ => stepStmt st s = o)
    (motive_5 := fun b o _ => stepBody st b = o)
  sound_intro
  case arrAccessCongr name index o hprem hih =>
    rw [stepExpr_arrayAccess_eq (StepExpr.not_isValue hprem), hih]
  case assignCongr lhs op rhs o hprem hih =>
    rw [stepExpr_assign_eq (StepLVal.not_isTarget hprem), hih]
  case assignTCongr target op rhs o hprem hih =>
    rw [stepExpr_assignTarget_eq (StepExpr.not_isValue hprem), hih]
  case relRhsCongr left op rhs tail o hprem hih =>
    rw [stepExpr_relRhs_eq (StepExpr.not_isValue hprem), hih]
  case relFirstCongr first rest o hprem hih =>
    rw [stepExpr_relFirst_eq (StepExpr.not_isValue hprem), hih]
  case binRCongr op left rhs o hprem hih =>
    rw [stepExpr_binR_eq (StepExpr.not_isValue hprem), hih]
  case binLCongr op lhs rhs o hprem hih =>
    rw [stepExpr_binL_eq (StepExpr.not_isValue hprem), hih]
  case negCongr arg o hprem hih =>
    rw [stepExpr_neg_eq (StepExpr.not_isValue hprem), hih]
  case bumpCongr op target o hprem hih =>
    rw [stepExpr_bump_eq (StepLVal.not_isTarget hprem), hih]
  case builtinCongr fn arg o hprem hih =>
    rw [stepExpr_builtin_eq (StepExpr.not_isValue hprem), hih]
  case parenCongr body o hprem hih =>
    rw [stepExpr_paren_eq (StepExpr.not_isValue hprem), hih]
  case arrCongr name index o hprem hih =>
    rw [stepLVal_array_eq (StepExpr.not_isValue hprem), hih]
  case exprStep expr rest o hprem hih =>
    rw [stepArgs_expr_eq (StepExpr.not_isValue hprem), hih]
  case exprCongr original expr o hprem hih =>
    rw [stepStmt_expr_eq (StepExpr.not_isValue hprem), hih]
  case evalCongr expr o hprem hih =>
    rw [stepStmt_eval_eq (StepExpr.not_isValue hprem), hih]
  case ifCongr cond thenBranch o hprem hih =>
    rw [stepStmt_ifThen_eq (StepExpr.not_isValue hprem), hih]
  case whileCongr condSource cond body o hprem hih =>
    rw [stepStmt_while_eq (StepExpr.not_isValue hprem), hih]
  case forCongr condSource cond updateSource body o hprem hih =>
    rw [stepStmt_forCheck_eq (StepExpr.not_isValue hprem), hih]
  case forUpdCongr condSource updateSource update body o hprem hih =>
    rw [stepStmt_forUpdate_eq (StepExpr.not_isValue hprem), hih]
  case retCongr expr o hprem hih =>
    rw [stepStmt_return_eq (StepExpr.not_isValue hprem), hih]

theorem stepArgs_sound {st a o} (h : StepArgs st a o) : stepArgs st a = o := by
  apply @StepArgs.rec st
    (motive_1 := fun e o _ => stepExpr st e = o)
    (motive_2 := fun lv o _ => stepLVal st lv = o)
    (motive_3 := fun a o _ => stepArgs st a = o)
    (motive_4 := fun s o _ => stepStmt st s = o)
    (motive_5 := fun b o _ => stepBody st b = o)
  sound_intro
  case arrAccessCongr name index o hprem hih =>
    rw [stepExpr_arrayAccess_eq (StepExpr.not_isValue hprem), hih]
  case assignCongr lhs op rhs o hprem hih =>
    rw [stepExpr_assign_eq (StepLVal.not_isTarget hprem), hih]
  case assignTCongr target op rhs o hprem hih =>
    rw [stepExpr_assignTarget_eq (StepExpr.not_isValue hprem), hih]
  case relRhsCongr left op rhs tail o hprem hih =>
    rw [stepExpr_relRhs_eq (StepExpr.not_isValue hprem), hih]
  case relFirstCongr first rest o hprem hih =>
    rw [stepExpr_relFirst_eq (StepExpr.not_isValue hprem), hih]
  case binRCongr op left rhs o hprem hih =>
    rw [stepExpr_binR_eq (StepExpr.not_isValue hprem), hih]
  case binLCongr op lhs rhs o hprem hih =>
    rw [stepExpr_binL_eq (StepExpr.not_isValue hprem), hih]
  case negCongr arg o hprem hih =>
    rw [stepExpr_neg_eq (StepExpr.not_isValue hprem), hih]
  case bumpCongr op target o hprem hih =>
    rw [stepExpr_bump_eq (StepLVal.not_isTarget hprem), hih]
  case builtinCongr fn arg o hprem hih =>
    rw [stepExpr_builtin_eq (StepExpr.not_isValue hprem), hih]
  case parenCongr body o hprem hih =>
    rw [stepExpr_paren_eq (StepExpr.not_isValue hprem), hih]
  case arrCongr name index o hprem hih =>
    rw [stepLVal_array_eq (StepExpr.not_isValue hprem), hih]
  case exprStep expr rest o hprem hih =>
    rw [stepArgs_expr_eq (StepExpr.not_isValue hprem), hih]
  case exprCongr original expr o hprem hih =>
    rw [stepStmt_expr_eq (StepExpr.not_isValue hprem), hih]
  case evalCongr expr o hprem hih =>
    rw [stepStmt_eval_eq (StepExpr.not_isValue hprem), hih]
  case ifCongr cond thenBranch o hprem hih =>
    rw [stepStmt_ifThen_eq (StepExpr.not_isValue hprem), hih]
  case whileCongr condSource cond body o hprem hih =>
    rw [stepStmt_while_eq (StepExpr.not_isValue hprem), hih]
  case forCongr condSource cond updateSource body o hprem hih =>
    rw [stepStmt_forCheck_eq (StepExpr.not_isValue hprem), hih]
  case forUpdCongr condSource updateSource update body o hprem hih =>
    rw [stepStmt_forUpdate_eq (StepExpr.not_isValue hprem), hih]
  case retCongr expr o hprem hih =>
    rw [stepStmt_return_eq (StepExpr.not_isValue hprem), hih]

theorem stepStmt_sound {st s o} (h : StepStmt st s o) : stepStmt st s = o := by
  apply @StepStmt.rec st
    (motive_1 := fun e o _ => stepExpr st e = o)
    (motive_2 := fun lv o _ => stepLVal st lv = o)
    (motive_3 := fun a o _ => stepArgs st a = o)
    (motive_4 := fun s o _ => stepStmt st s = o)
    (motive_5 := fun b o _ => stepBody st b = o)
  sound_intro
  case arrAccessCongr name index o hprem hih =>
    rw [stepExpr_arrayAccess_eq (StepExpr.not_isValue hprem), hih]
  case assignCongr lhs op rhs o hprem hih =>
    rw [stepExpr_assign_eq (StepLVal.not_isTarget hprem), hih]
  case assignTCongr target op rhs o hprem hih =>
    rw [stepExpr_assignTarget_eq (StepExpr.not_isValue hprem), hih]
  case relRhsCongr left op rhs tail o hprem hih =>
    rw [stepExpr_relRhs_eq (StepExpr.not_isValue hprem), hih]
  case relFirstCongr first rest o hprem hih =>
    rw [stepExpr_relFirst_eq (StepExpr.not_isValue hprem), hih]
  case binRCongr op left rhs o hprem hih =>
    rw [stepExpr_binR_eq (StepExpr.not_isValue hprem), hih]
  case binLCongr op lhs rhs o hprem hih =>
    rw [stepExpr_binL_eq (StepExpr.not_isValue hprem), hih]
  case negCongr arg o hprem hih =>
    rw [stepExpr_neg_eq (StepExpr.not_isValue hprem), hih]
  case bumpCongr op target o hprem hih =>
    rw [stepExpr_bump_eq (StepLVal.not_isTarget hprem), hih]
  case builtinCongr fn arg o hprem hih =>
    rw [stepExpr_builtin_eq (StepExpr.not_isValue hprem), hih]
  case parenCongr body o hprem hih =>
    rw [stepExpr_paren_eq (StepExpr.not_isValue hprem), hih]
  case arrCongr name index o hprem hih =>
    rw [stepLVal_array_eq (StepExpr.not_isValue hprem), hih]
  case exprStep expr rest o hprem hih =>
    rw [stepArgs_expr_eq (StepExpr.not_isValue hprem), hih]
  case exprCongr original expr o hprem hih =>
    rw [stepStmt_expr_eq (StepExpr.not_isValue hprem), hih]
  case evalCongr expr o hprem hih =>
    rw [stepStmt_eval_eq (StepExpr.not_isValue hprem), hih]
  case ifCongr cond thenBranch o hprem hih =>
    rw [stepStmt_ifThen_eq (StepExpr.not_isValue hprem), hih]
  case whileCongr condSource cond body o hprem hih =>
    rw [stepStmt_while_eq (StepExpr.not_isValue hprem), hih]
  case forCongr condSource cond updateSource body o hprem hih =>
    rw [stepStmt_forCheck_eq (StepExpr.not_isValue hprem), hih]
  case forUpdCongr condSource updateSource update body o hprem hih =>
    rw [stepStmt_forUpdate_eq (StepExpr.not_isValue hprem), hih]
  case retCongr expr o hprem hih =>
    rw [stepStmt_return_eq (StepExpr.not_isValue hprem), hih]

theorem stepBody_sound {st b o} (h : StepBody st b o) : stepBody st b = o := by
  apply @StepBody.rec st
    (motive_1 := fun e o _ => stepExpr st e = o)
    (motive_2 := fun lv o _ => stepLVal st lv = o)
    (motive_3 := fun a o _ => stepArgs st a = o)
    (motive_4 := fun s o _ => stepStmt st s = o)
    (motive_5 := fun b o _ => stepBody st b = o)
  sound_intro
  case arrAccessCongr name index o hprem hih =>
    rw [stepExpr_arrayAccess_eq (StepExpr.not_isValue hprem), hih]
  case assignCongr lhs op rhs o hprem hih =>
    rw [stepExpr_assign_eq (StepLVal.not_isTarget hprem), hih]
  case assignTCongr target op rhs o hprem hih =>
    rw [stepExpr_assignTarget_eq (StepExpr.not_isValue hprem), hih]
  case relRhsCongr left op rhs tail o hprem hih =>
    rw [stepExpr_relRhs_eq (StepExpr.not_isValue hprem), hih]
  case relFirstCongr first rest o hprem hih =>
    rw [stepExpr_relFirst_eq (StepExpr.not_isValue hprem), hih]
  case binRCongr op left rhs o hprem hih =>
    rw [stepExpr_binR_eq (StepExpr.not_isValue hprem), hih]
  case binLCongr op lhs rhs o hprem hih =>
    rw [stepExpr_binL_eq (StepExpr.not_isValue hprem), hih]
  case negCongr arg o hprem hih =>
    rw [stepExpr_neg_eq (StepExpr.not_isValue hprem), hih]
  case bumpCongr op target o hprem hih =>
    rw [stepExpr_bump_eq (StepLVal.not_isTarget hprem), hih]
  case builtinCongr fn arg o hprem hih =>
    rw [stepExpr_builtin_eq (StepExpr.not_isValue hprem), hih]
  case parenCongr body o hprem hih =>
    rw [stepExpr_paren_eq (StepExpr.not_isValue hprem), hih]
  case arrCongr name index o hprem hih =>
    rw [stepLVal_array_eq (StepExpr.not_isValue hprem), hih]
  case exprStep expr rest o hprem hih =>
    rw [stepArgs_expr_eq (StepExpr.not_isValue hprem), hih]
  case exprCongr original expr o hprem hih =>
    rw [stepStmt_expr_eq (StepExpr.not_isValue hprem), hih]
  case evalCongr expr o hprem hih =>
    rw [stepStmt_eval_eq (StepExpr.not_isValue hprem), hih]
  case ifCongr cond thenBranch o hprem hih =>
    rw [stepStmt_ifThen_eq (StepExpr.not_isValue hprem), hih]
  case whileCongr condSource cond body o hprem hih =>
    rw [stepStmt_while_eq (StepExpr.not_isValue hprem), hih]
  case forCongr condSource cond updateSource body o hprem hih =>
    rw [stepStmt_forCheck_eq (StepExpr.not_isValue hprem), hih]
  case forUpdCongr condSource updateSource update body o hprem hih =>
    rw [stepStmt_forUpdate_eq (StepExpr.not_isValue hprem), hih]
  case retCongr expr o hprem hih =>
    rw [stepStmt_return_eq (StepExpr.not_isValue hprem), hih]

theorem stepProg_sound {c o} (h : StepProg c o) : step c = o := by
  cases h with
  | nil => rfl
  | quit hquit =>
      simp [step, hquit]
  | funDef hquit =>
      simp [step, next, hquit]
  | stmt hquit hstmt =>
      rw [step]
      simp [next, liftProg, hquit, stepStmt_sound hstmt]
      rfl

/-! ### Completeness: every executable step is derivable -/

mutual

theorem stepExpr_complete {st e} (h : ExprTerm.isValue e = false) :
    StepExpr st e (stepExpr st e) := by
  cases e with
  | value value => simp [ExprTerm.isValue] at h
  | num raw => simpa [stepExpr] using (StepExpr.num (st := st) (raw := raw))
  | var name => simpa [stepExpr] using (StepExpr.var (st := st) (name := name))
  | special v => simpa [stepExpr] using (StepExpr.special (st := st) (v := v))
  | arrayAccess name index =>
      cases index
      case value indexValue =>
        cases hidx : indexOfNum? indexValue with
        | ok idx =>
            cases hensure : ensureArrayId st name with
            | mk st' id =>
                simpa [stepExpr, hidx, hensure] using
                  (StepExpr.arrAccessOk (st := st) (st' := st') (name := name)
                    (idxValue := indexValue) (idx := idx) (id := id) hidx hensure)
        | error msg =>
            simpa [stepExpr, hidx] using
              (StepExpr.arrAccessErr (st := st) (name := name) (idxValue := indexValue)
                (msg := msg) hidx)
      all_goals
        rw [stepExpr_arrayAccess_eq (by rfl)]
        exact StepExpr.arrAccessCongr (stepExpr_complete (st := st) (e := _) (by rfl))
  | assign lhs op rhs =>
      cases lhs
      case target target =>
        simpa [stepExpr] using
          (StepExpr.assignTarget0 (st := st) (target := target) (op := op) (rhs := rhs))
      all_goals
        rw [stepExpr_assign_eq (by rfl)]
        exact StepExpr.assignCongr (stepLVal_complete (st := st) (lv := _) (by rfl))
  | assignTarget target op rhs =>
      cases rhs
      case value rhsValue =>
        cases hassign : applyAssign? op (readLValueTarget st target) rhsValue st.scale with
        | ok result =>
            simpa [stepExpr, hassign] using
              (StepExpr.assignTOk (st := st) (target := target) (op := op)
                (rhsValue := rhsValue) (result := result) hassign)
        | error msg =>
            simpa [stepExpr, hassign] using
              (StepExpr.assignTErr (st := st) (target := target) (op := op)
                (rhsValue := rhsValue) (msg := msg) hassign)
      all_goals
        rw [stepExpr_assignTarget_eq (by rfl)]
        exact StepExpr.assignTCongr (stepExpr_complete (st := st) (e := _) (by rfl))
  | rel first rest =>
      cases first
      case value left =>
        cases rest with
        | nil =>
            simpa [stepExpr] using (StepExpr.relNil (st := st) (left := left))
        | cons head tail =>
            cases head with
            | mk op rhs =>
                cases rhs
                case value right =>
                  cases tail with
                  | nil =>
                      simpa [stepExpr] using
                        (StepExpr.relDone (st := st) (left := left) (op := op)
                          (right := right))
                  | cons pair tail' =>
                      simpa [stepExpr] using
                        (StepExpr.relCons (st := st) (left := left) (op := op)
                          (right := right) (pair := pair) (tail := tail'))
                all_goals
                  rw [stepExpr_relRhs_eq (by rfl)]
                  exact StepExpr.relRhsCongr
                    (stepExpr_complete (st := st) (e := _) (by rfl))
      all_goals
        rw [stepExpr_relFirst_eq (by rfl)]
        exact StepExpr.relFirstCongr (stepExpr_complete (st := st) (e := _) (by rfl))
  | bin op lhs rhs =>
      cases lhs
      case value left =>
        cases rhs
        case value right =>
          cases hbin : applyBin? op left right st.scale with
          | ok result =>
              simpa [stepExpr, hbin] using
                (StepExpr.binOk (st := st) (op := op) (left := left) (right := right)
                  (result := result) hbin)
          | error msg =>
              simpa [stepExpr, hbin] using
                (StepExpr.binErr (st := st) (op := op) (left := left) (right := right)
                  (msg := msg) hbin)
        all_goals
          rw [stepExpr_binR_eq (by rfl)]
          exact StepExpr.binRCongr (stepExpr_complete (st := st) (e := _) (by rfl))
      all_goals
        rw [stepExpr_binL_eq (by rfl)]
        exact StepExpr.binLCongr (stepExpr_complete (st := st) (e := _) (by rfl))
  | neg arg =>
      cases arg
      case value value =>
        simpa [stepExpr] using (StepExpr.negVal (st := st) (value := value))
      all_goals
        rw [stepExpr_neg_eq (by rfl)]
        exact StepExpr.negCongr (stepExpr_complete (st := st) (e := _) (by rfl))
  | bump op target =>
      cases target
      case target target =>
        simpa [stepExpr, bumpOutcome] using
          (StepExpr.bumpTarget (st := st) (op := op) (target := target))
      all_goals
        rw [stepExpr_bump_eq (by rfl)]
        exact StepExpr.bumpCongr (stepLVal_complete (st := st) (lv := _) (by rfl))
  | badBump op arg =>
      simpa [stepExpr] using (StepExpr.badBump (st := st) (op := op) (arg := arg))
  | call name args =>
      cases hfun : lookupFunction st name with
      | none =>
          simpa [stepExpr, hfun] using
            (StepExpr.callUndef (st := st) (name := name) (args := args) hfun)
      | some defn =>
          simpa [stepExpr, hfun, liftAE] using
            (StepExpr.callDef (st := st) (name := name) (args := args) (defn := defn)
              hfun (stepArgs_complete (st := st) (a := args)))
  | activeCall body =>
      simpa [stepExpr, liftActiveCall] using
        (StepExpr.activeCall (st := st) (body := body)
          (stepBody_complete (st := st) (b := body)))
  | builtin fn arg =>
      cases arg with
      | none =>
          simpa [stepExpr] using (StepExpr.builtinNone (st := st) (fn := fn))
      | some arg =>
          cases arg
          case value value =>
            cases hbuiltin : applyBuiltin? fn value st.scale with
            | ok result =>
                simpa [stepExpr, hbuiltin] using
                  (StepExpr.builtinOk (st := st) (fn := fn) (value := value)
                    (result := result) hbuiltin)
            | error msg =>
                simpa [stepExpr, hbuiltin] using
                  (StepExpr.builtinErr (st := st) (fn := fn) (value := value)
                    (msg := msg) hbuiltin)
          all_goals
            rw [stepExpr_builtin_eq (by rfl)]
            exact StepExpr.builtinCongr
              (stepExpr_complete (st := st) (e := _) (by rfl))
  | paren body =>
      cases body
      case value value =>
        simpa [stepExpr] using (StepExpr.parenVal (st := st) (value := value))
      all_goals
        rw [stepExpr_paren_eq (by rfl)]
        exact StepExpr.parenCongr (stepExpr_complete (st := st) (e := _) (by rfl))

theorem stepLVal_complete {st lv} (h : LValTerm.isTarget lv = false) :
    StepLVal st lv (stepLVal st lv) := by
  cases lv with
  | target target => simp [LValTerm.isTarget] at h
  | var name => simpa [stepLVal] using (StepLVal.var (st := st) (name := name))
  | special v => simpa [stepLVal] using (StepLVal.special (st := st) (v := v))
  | array name index =>
      cases index
      case value indexValue =>
        cases hidx : indexOfNum? indexValue with
        | ok idx =>
            cases hensure : ensureArrayId st name with
            | mk st' id =>
                simpa [stepLVal, hidx, hensure] using
                  (StepLVal.arrOk (st := st) (st' := st') (name := name)
                    (idxValue := indexValue) (idx := idx) (id := id) hidx hensure)
        | error msg =>
            simpa [stepLVal, hidx] using
              (StepLVal.arrErr (st := st) (name := name) (idxValue := indexValue)
                (msg := msg) hidx)
      all_goals
        rw [stepLVal_array_eq (by rfl)]
        exact StepLVal.arrCongr (stepExpr_complete (st := st) (e := _) (by rfl))

theorem stepArgs_complete {st a} : StepArgs st a (stepArgs st a) := by
  cases a with
  | nil => simpa [stepArgs] using (StepArgs.nil (st := st))
  | cons arg rest =>
      cases arg with
      | arrayRef name =>
          simpa [stepArgs, liftArgsTail] using
            (StepArgs.arrayRef (st := st) (name := name) (rest := rest)
              (stepArgs_complete (st := st) (a := rest)))
      | expr expr =>
          cases expr
          case value value =>
            simpa [stepArgs, liftArgsTail] using
              (StepArgs.exprVal (st := st) (value := value) (rest := rest)
                (stepArgs_complete (st := st) (a := rest)))
          all_goals
            rw [stepArgs_expr_eq (by rfl)]
            exact StepArgs.exprStep (stepExpr_complete (st := st) (e := _) (by rfl))

theorem stepStmt_complete {st s} : StepStmt st s (stepStmt st s) := by
  cases s with
  | done => simpa [stepStmt] using (StepStmt.done (st := st))
  | expr original expr =>
      cases expr
      case value value =>
        cases hassign : isTopAssignment original with
        | false =>
            simpa [stepStmt, hassign] using
              (StepStmt.exprPrint (st := st) (original := original) (value := value)
                (by simpa using hassign))
        | true =>
            simpa [stepStmt, hassign] using
              (StepStmt.exprAssign (st := st) (original := original) (value := value)
                (by simpa using hassign))
      all_goals
        rw [stepStmt_expr_eq (by rfl)]
        exact StepStmt.exprCongr (stepExpr_complete (st := st) (e := _) (by rfl))
  | eval expr =>
      cases expr
      case value value =>
        simpa [stepStmt] using (StepStmt.evalVal (st := st) (value := value))
      all_goals
        rw [stepStmt_eval_eq (by rfl)]
        exact StepStmt.evalCongr (stepExpr_complete (st := st) (e := _) (by rfl))
  | str s => simpa [stepStmt] using (StepStmt.str (st := st) (s := s))
  | auto params => simpa [stepStmt] using (StepStmt.auto (st := st) (params := params))
  | ifThen cond thenBranch =>
      cases cond
      case value cond =>
        cases hzero : cond.isZero with
        | false =>
            simpa [stepStmt, hzero] using
              (StepStmt.ifTrue (st := st) (cond := cond) (thenBranch := thenBranch)
                (by simpa using hzero))
        | true =>
            simpa [stepStmt, hzero] using
              (StepStmt.ifFalse (st := st) (cond := cond) (thenBranch := thenBranch)
                (by simpa using hzero))
      all_goals
        rw [stepStmt_ifThen_eq (by rfl)]
        exact StepStmt.ifCongr (stepExpr_complete (st := st) (e := _) (by rfl))
  | «while» condSource cond body =>
      cases cond
      case value cond =>
        cases hzero : cond.isZero with
        | false =>
            simpa [stepStmt, hzero] using
              (StepStmt.whileTrue (st := st) (condSource := condSource) (cond := cond)
                (body := body) (by simpa using hzero))
        | true =>
            simpa [stepStmt, hzero] using
              (StepStmt.whileFalse (st := st) (condSource := condSource) (cond := cond)
                (body := body) (by simpa using hzero))
      all_goals
        rw [stepStmt_while_eq (by rfl)]
        exact StepStmt.whileCongr (stepExpr_complete (st := st) (e := _) (by rfl))
  | forCheck condSource cond updateSource body =>
      cases cond
      case value cond =>
        cases hzero : cond.isZero with
        | false =>
            simpa [stepStmt, hzero] using
              (StepStmt.forTrue (st := st) (condSource := condSource) (cond := cond)
                (updateSource := updateSource) (body := body) (by simpa using hzero))
        | true =>
            simpa [stepStmt, hzero] using
              (StepStmt.forFalse (st := st) (condSource := condSource) (cond := cond)
                (updateSource := updateSource) (body := body) (by simpa using hzero))
      all_goals
        rw [stepStmt_forCheck_eq (by rfl)]
        exact StepStmt.forCongr (stepExpr_complete (st := st) (e := _) (by rfl))
  | forUpdate condSource updateSource update body =>
      cases update
      case value value =>
        simpa [stepStmt] using
          (StepStmt.forUpdVal (st := st) (condSource := condSource)
            (updateSource := updateSource) (value := value) (body := body))
      all_goals
        rw [stepStmt_forUpdate_eq (by rfl)]
        exact StepStmt.forUpdCongr (stepExpr_complete (st := st) (e := _) (by rfl))
  | loopBody body after =>
      cases body
      case done => simpa [stepStmt] using (StepStmt.loopDone (st := st) (after := after))
      all_goals
        rw [stepStmt_loopBody_eq (by intro hdone; cases hdone)]
        exact StepStmt.loopCongr (by intro hdone; cases hdone)
          (stepStmt_complete (st := st) (s := _))
  | seq first second =>
      cases first
      case done => simpa [stepStmt] using (StepStmt.seqDone (st := st) (second := second))
      all_goals
        rw [stepStmt_seq_eq (by intro hdone; cases hdone)]
        exact StepStmt.seqCongr (by intro hdone; cases hdone)
          (stepStmt_complete (st := st) (s := _))
  | «break» => simpa [stepStmt] using (StepStmt.breakStmt (st := st))
  | «return» value =>
      cases value with
      | none => simpa [stepStmt] using (StepStmt.retNone (st := st))
      | some expr =>
          cases expr
          case value value =>
            simpa [stepStmt] using (StepStmt.retVal (st := st) (value := value))
          all_goals
            rw [stepStmt_return_eq (by rfl)]
            exact StepStmt.retCongr (stepExpr_complete (st := st) (e := _) (by rfl))
  | quit => simpa [stepStmt] using (StepStmt.quitStmt (st := st))
  | block body =>
      simpa [stepStmt, liftBlock] using
        (StepStmt.block (st := st) (body := body)
          (stepBody_complete (st := st) (b := body)))

theorem stepBody_complete {st b} : StepBody st b (stepBody st b) := by
  cases b with
  | stmts stmts =>
      cases stmts with
      | nil => simpa [stepBody] using (StepBody.nil (st := st))
      | cons stmt rest =>
          simpa [stepBody, liftBodyStep] using
            (StepBody.cons (st := st) (stmt := stmt) (rest := rest)
              (stepStmt_complete (st := st) (s := stmt)))

end

theorem stepProg_complete {c} : StepProg c (step c) := by
  cases c with
  | mk st program =>
      cases program with
      | nil =>
          simpa [step] using (StepProg.nil (st := st))
      | cons item rest =>
          cases hquit : TopItemTerm.containsQuit item with
          | false =>
              cases item with
              | funDef defn =>
                  simpa [step, next, hquit] using
                    (StepProg.funDef (st := st) (defn := defn) (rest := rest) hquit)
              | stmt stmt =>
                  simpa [step, next, liftProg, hquit] using
                    (StepProg.stmt (st := st) (stmt := stmt) (rest := rest) hquit
                      (stepStmt_complete (st := st) (s := stmt)))
          | true =>
              simpa [step, hquit] using
                (StepProg.quit (st := st) (item := item) (rest := rest) hquit)

theorem stepProg_iff (c o) : StepProg c o ↔ step c = o := by
  constructor
  · exact stepProg_sound
  · intro h
    rw [← h]
    exact stepProg_complete (c := c)

theorem stepProg_deterministic {c o₁ o₂} :
    StepProg c o₁ → StepProg c o₂ → o₁ = o₂ := by
  intro h₁ h₂
  exact ((stepProg_iff c o₁).mp h₁).symm.trans ((stepProg_iff c o₂).mp h₂)

end SmallStep

end Bc
