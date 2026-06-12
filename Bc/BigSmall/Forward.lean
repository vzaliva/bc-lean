/-
  Forward simulation from terminating big-step evaluation to finite small-step runs.
-/

import Bc.BigSmall.Expr
import Bc.BigSmall.Run
import Bc.SmallStepProperties

namespace Bc

namespace BigSmall

open SmallStep

def EvalResultNotFuel {α : Type} : EvalResult α → Prop
  | .outOfFuel _ => False
  | _ => True

def ResultNotFuel {α : Type} : Result α → Prop
  | .outOfFuel _ => False
  | _ => True

def evalToStmtOutcome : Result Control → StmtOutcome
  | .ok st .normal => .done st
  | .ok st c => .control st c
  | .outOfFuel st => .runtimeError st "internal outOfFuel"
  | .runtimeError st msg => .runtimeError st msg

def evalToBodyOutcome : Result Control → BodyOutcome
  | .ok st .normal => .done st
  | .ok st c => .control st c
  | .outOfFuel st => .runtimeError st "internal outOfFuel"
  | .runtimeError st msg => .runtimeError st msg

private structure ForwardProps (fuel : Nat) : Prop where
  expr : ∀ st e r, evalExpr fuel st e = r → EvalResultNotFuel r →
    ExprRuns st (ExprTerm.ofExpr e) (evalToExprOutcome r)
  rel : ∀ st left rest r, evalRelChain fuel st left rest = r → EvalResultNotFuel r →
    ExprRuns st (.rel (.value left) (ExprTerm.ofRelRest rest)) (evalToExprOutcome r)
  lval : ∀ st lv r, evalLValueTarget fuel st lv = r → EvalResultNotFuel r →
    LValRuns st (LValTerm.ofLVal lv) (evalToLValOutcome r)
  assign : ∀ st lhs op rhs r, evalAssign fuel st lhs op rhs = r → EvalResultNotFuel r →
    ExprRuns st (.assign (LValTerm.ofLVal lhs) op (ExprTerm.ofExpr rhs))
      (evalToExprOutcome r)
  unary : ∀ st op arg r, evalUnary fuel st op arg = r → EvalResultNotFuel r →
    ExprRuns st (ExprTerm.ofExpr (.unary op arg)) (evalToExprOutcome r)
  builtin : ∀ st fn arg r, evalBuiltin fuel st fn arg = r → EvalResultNotFuel r →
    ExprRuns st (ExprTerm.ofExpr (.builtin fn arg)) (evalToExprOutcome r)
  args : ∀ st args r, evalArgValues fuel st args = r → EvalResultNotFuel r →
    ArgsRuns st (ArgTerm.ofArgs args) (evalToArgsOutcome r)
  call : ∀ st name args r, evalCall fuel st name args = r → EvalResultNotFuel r →
    ExprRuns st (.call name (ArgTerm.ofArgs args)) (evalToExprOutcome r)
  stmt : ∀ st stmt r, evalStmt fuel st stmt = r → ResultNotFuel r →
    StmtRuns st (StmtTerm.ofStmt stmt) (evalToStmtOutcome r)
  forLoop : ∀ st cond update body r, evalFor fuel st cond update body = r →
    ResultNotFuel r →
    StmtRuns st (.forCheck cond (ExprTerm.ofExpr cond) update (StmtTerm.ofStmt body))
      (evalToStmtOutcome r)
  stmts : ∀ st stmts r, evalStmts fuel st stmts = r → ResultNotFuel r →
    BodyRuns st (.stmts (StmtTerm.ofStmts stmts)) (evalToBodyOutcome r)
  body : ∀ st body r, evalBody fuel st body = r → ResultNotFuel r →
    BodyRuns st (BodyTerm.ofBody body) (evalToBodyOutcome r)

private theorem evalResultNotFuel_of_eq {α : Type} {r r' : EvalResult α}
    (h : r = r') (hnf : EvalResultNotFuel r') : EvalResultNotFuel r := by
  subst h
  exact hnf

private theorem resultNotFuel_of_eq {α : Type} {r r' : Result α}
    (h : r = r') (hnf : ResultNotFuel r') : ResultNotFuel r := by
  subst h
  exact hnf

theorem stepExpr_arrayAccess_next {name : Name} {st e st' e'}
    (h : stepExpr st e = .next st' e') :
    stepExpr st (.arrayAccess name e) = .next st' (.arrayAccess name e') := by
  cases e <;> simp_all [stepExpr]
  all_goals first | rfl | (rcases h with ⟨hst, he⟩; subst hst; subst he; rfl)

theorem stepExpr_arrayAccess_control {name : Name} {st e st' c}
    (h : stepExpr st e = .control st' c) :
    stepExpr st (.arrayAccess name e) = .control st' c := by
  cases e <;> simp_all [stepExpr]

theorem stepExpr_arrayAccess_error {name : Name} {st e st' msg}
    (h : stepExpr st e = .runtimeError st' msg) :
    stepExpr st (.arrayAccess name e) = .runtimeError st' msg := by
  cases e <;> simp_all [stepExpr]

theorem stepLVal_array_next {name : Name} {st e st' e'}
    (h : stepExpr st e = .next st' e') :
    stepLVal st (.array name e) = .next st' (.array name e') := by
  cases e <;> simp_all [stepLVal, stepExpr]
  all_goals first | rfl | (rcases h with ⟨hst, he⟩; subst hst; subst he; rfl)

theorem stepLVal_array_control {name : Name} {st e st' c}
    (h : stepExpr st e = .control st' c) :
    stepLVal st (.array name e) =
      .runtimeError st' "control escaped from lvalue evaluation" := by
  cases e <;> simp_all [stepLVal, stepExpr]

theorem stepLVal_array_error {name : Name} {st e st' msg}
    (h : stepExpr st e = .runtimeError st' msg) :
    stepLVal st (.array name e) = .runtimeError st' msg := by
  cases e <;> simp_all [stepLVal, stepExpr]

theorem stepExpr_assign_lval_next {op : AssignOp} {rhs : ExprTerm}
    {st lv st' lv'} (h : stepLVal st lv = .next st' lv') :
    stepExpr st (.assign lv op rhs) = .next st' (.assign lv' op rhs) := by
  cases lv with
  | target target => simp [stepLVal] at h
  | var name =>
      change
        (match stepLVal st (.var name) with
        | LValOutcome.next stx lvx => ExprOutcome.next stx (.assign lvx op rhs)
        | LValOutcome.target stx target => ExprOutcome.next stx (.assignTarget target op rhs)
        | LValOutcome.runtimeError stx msg => ExprOutcome.runtimeError stx msg) =
          ExprOutcome.next st' (.assign lv' op rhs)
      rw [h]
  | special v =>
      change
        (match stepLVal st (.special v) with
        | LValOutcome.next stx lvx => ExprOutcome.next stx (.assign lvx op rhs)
        | LValOutcome.target stx target => ExprOutcome.next stx (.assignTarget target op rhs)
        | LValOutcome.runtimeError stx msg => ExprOutcome.runtimeError stx msg) =
          ExprOutcome.next st' (.assign lv' op rhs)
      rw [h]
  | array name index =>
      change
        (match stepLVal st (.array name index) with
        | LValOutcome.next stx lvx => ExprOutcome.next stx (.assign lvx op rhs)
        | LValOutcome.target stx target => ExprOutcome.next stx (.assignTarget target op rhs)
        | LValOutcome.runtimeError stx msg => ExprOutcome.runtimeError stx msg) =
          ExprOutcome.next st' (.assign lv' op rhs)
      rw [h]

theorem stepExpr_assign_lval_error {op : AssignOp} {rhs : ExprTerm}
    {st lv st' msg} (h : stepLVal st lv = .runtimeError st' msg) :
    stepExpr st (.assign lv op rhs) = .runtimeError st' msg := by
  cases lv with
  | target target => simp [stepLVal] at h
  | var name =>
      change
        (match stepLVal st (.var name) with
        | LValOutcome.next stx lvx => ExprOutcome.next stx (.assign lvx op rhs)
        | LValOutcome.target stx target => ExprOutcome.next stx (.assignTarget target op rhs)
        | LValOutcome.runtimeError stx msg => ExprOutcome.runtimeError stx msg) =
          ExprOutcome.runtimeError st' msg
      rw [h]
  | special v =>
      change
        (match stepLVal st (.special v) with
        | LValOutcome.next stx lvx => ExprOutcome.next stx (.assign lvx op rhs)
        | LValOutcome.target stx target => ExprOutcome.next stx (.assignTarget target op rhs)
        | LValOutcome.runtimeError stx msg => ExprOutcome.runtimeError stx msg) =
          ExprOutcome.runtimeError st' msg
      rw [h]
  | array name index =>
      change
        (match stepLVal st (.array name index) with
        | LValOutcome.next stx lvx => ExprOutcome.next stx (.assign lvx op rhs)
        | LValOutcome.target stx target => ExprOutcome.next stx (.assignTarget target op rhs)
        | LValOutcome.runtimeError stx msg => ExprOutcome.runtimeError stx msg) =
          ExprOutcome.runtimeError st' msg
      rw [h]

theorem stepExpr_assignTarget_rhs_next {target : LValueTarget} {op : AssignOp}
    {st rhs st' rhs'} (h : stepExpr st rhs = .next st' rhs') :
    stepExpr st (.assignTarget target op rhs) = .next st' (.assignTarget target op rhs') := by
  cases rhs <;> simp_all [stepExpr]
  all_goals first | rfl | (rcases h with ⟨hst, he⟩; subst hst; subst he; rfl)

theorem stepExpr_assignTarget_rhs_control {target : LValueTarget} {op : AssignOp}
    {st rhs st' c} (h : stepExpr st rhs = .control st' c) :
    stepExpr st (.assignTarget target op rhs) = .control st' c := by
  cases rhs <;> simp_all [stepExpr]

theorem stepExpr_assignTarget_rhs_error {target : LValueTarget} {op : AssignOp}
    {st rhs st' msg} (h : stepExpr st rhs = .runtimeError st' msg) :
    stepExpr st (.assignTarget target op rhs) = .runtimeError st' msg := by
  cases rhs <;> simp_all [stepExpr]

theorem stepExpr_bin_lhs_next {op : BinOp} {rhs : ExprTerm}
    {st lhs st' lhs'} (h : stepExpr st lhs = .next st' lhs') :
    stepExpr st (.bin op lhs rhs) = .next st' (.bin op lhs' rhs) := by
  cases lhs <;> simp_all [stepExpr]
  all_goals first | rfl | (rcases h with ⟨hst, he⟩; subst hst; subst he; rfl)

theorem stepExpr_bin_lhs_control {op : BinOp} {rhs : ExprTerm}
    {st lhs st' c} (h : stepExpr st lhs = .control st' c) :
    stepExpr st (.bin op lhs rhs) = .control st' c := by
  cases lhs <;> simp_all [stepExpr]

theorem stepExpr_bin_lhs_error {op : BinOp} {rhs : ExprTerm}
    {st lhs st' msg} (h : stepExpr st lhs = .runtimeError st' msg) :
    stepExpr st (.bin op lhs rhs) = .runtimeError st' msg := by
  cases lhs <;> simp_all [stepExpr]

theorem stepExpr_bin_rhs_next {op : BinOp} {left : Num}
    {st rhs st' rhs'} (h : stepExpr st rhs = .next st' rhs') :
    stepExpr st (.bin op (.value left) rhs) = .next st' (.bin op (.value left) rhs') := by
  cases rhs <;> simp_all [stepExpr]
  all_goals first | rfl | (rcases h with ⟨hst, he⟩; subst hst; subst he; rfl)

theorem stepExpr_paren_next {st e st' e'}
    (h : stepExpr st e = .next st' e') :
    stepExpr st (.paren e) = .next st' (.paren e') := by
  cases e <;> simp_all [stepExpr]
  all_goals first | rfl | (rcases h with ⟨hst, he⟩; subst hst; subst he; rfl)

theorem stepExpr_paren_control {st e st' c}
    (h : stepExpr st e = .control st' c) :
    stepExpr st (.paren e) = .control st' c := by
  cases e <;> simp_all [stepExpr]

theorem stepExpr_paren_error {st e st' msg}
    (h : stepExpr st e = .runtimeError st' msg) :
    stepExpr st (.paren e) = .runtimeError st' msg := by
  cases e <;> simp_all [stepExpr]

private theorem ExprRuns.paren_value {st n} :
    ExprRuns st (.paren (.value n)) (.value st n) := by
  exact ExprRuns.next (by simp [stepExpr]) ExprRuns.value

private theorem ExprRuns.bin_values_ok {st op a b n}
    (h : applyBin? op a b st.scale = .ok n) :
    ExprRuns st (.bin op (.value a) (.value b)) (.value st n) := by
  exact ExprRuns.next (by simp [stepExpr, h]) ExprRuns.value

private theorem ExprRuns.bin_values_error {st op a b msg}
    (h : applyBin? op a b st.scale = .error msg) :
    ExprRuns st (.bin op (.value a) (.value b)) (.runtimeError st msg) := by
  exact ExprRuns.runtimeError (by simp [stepExpr, h])

private theorem ExprRuns.assignTarget_value_ok {st target op rhsValue result}
    (h : applyAssign? op (readLValueTarget st target) rhsValue st.scale = .ok result) :
    ExprRuns st (.assignTarget target op (.value rhsValue))
      (.value (writeLValueTarget st target result) result) := by
  exact ExprRuns.next (by simp [stepExpr, h]) ExprRuns.value

private theorem ExprRuns.assignTarget_value_error {st target op rhsValue msg}
    (h : applyAssign? op (readLValueTarget st target) rhsValue st.scale = .error msg) :
    ExprRuns st (.assignTarget target op (.value rhsValue)) (.runtimeError st msg) := by
  exact ExprRuns.runtimeError (by simp [stepExpr, h])

theorem stepExpr_builtin_arg_next {fn : Builtin} {st e st' e'}
    (h : stepExpr st e = .next st' e') :
    stepExpr st (.builtin fn (some e)) = .next st' (.builtin fn (some e')) := by
  cases e <;> simp_all [stepExpr]
  all_goals first | rfl | (rcases h with ⟨hst, he⟩; subst hst; subst he; rfl)

theorem stepExpr_builtin_arg_control {fn : Builtin} {st e st' c}
    (h : stepExpr st e = .control st' c) :
    stepExpr st (.builtin fn (some e)) = .control st' c := by
  cases e <;> simp_all [stepExpr]

theorem stepExpr_builtin_arg_error {fn : Builtin} {st e st' msg}
    (h : stepExpr st e = .runtimeError st' msg) :
    stepExpr st (.builtin fn (some e)) = .runtimeError st' msg := by
  cases e <;> simp_all [stepExpr]

private theorem ExprRuns.builtin_none {st fn} :
    ExprRuns st (.builtin fn none) (.runtimeError st "invalid builtin arity") := by
  exact ExprRuns.runtimeError (by simp [stepExpr])

private theorem ExprRuns.builtin_value_ok {st fn value result}
    (h : applyBuiltin? fn value st.scale = .ok result) :
    ExprRuns st (.builtin fn (some (.value value))) (.value st result) := by
  exact ExprRuns.next (by simp [stepExpr, h]) ExprRuns.value

private theorem ExprRuns.builtin_value_error {st fn value msg}
    (h : applyBuiltin? fn value st.scale = .error msg) :
    ExprRuns st (.builtin fn (some (.value value))) (.runtimeError st msg) := by
  exact ExprRuns.runtimeError (by simp [stepExpr, h])

theorem stepExpr_neg_next {st e st' e'}
    (h : stepExpr st e = .next st' e') :
    stepExpr st (.neg e) = .next st' (.neg e') := by
  cases e <;> simp_all [stepExpr]
  all_goals first | rfl | (rcases h with ⟨hst, he⟩; subst hst; subst he; rfl)

theorem stepExpr_neg_control {st e st' c}
    (h : stepExpr st e = .control st' c) :
    stepExpr st (.neg e) = .control st' c := by
  cases e <;> simp_all [stepExpr]

theorem stepExpr_neg_error {st e st' msg}
    (h : stepExpr st e = .runtimeError st' msg) :
    stepExpr st (.neg e) = .runtimeError st' msg := by
  cases e <;> simp_all [stepExpr]

private theorem ExprRuns.neg_value {st value} :
    ExprRuns st (.neg (.value value)) (.value st (Num.neg value)) := by
  exact ExprRuns.next (by simp [stepExpr]) ExprRuns.value

theorem stepExpr_bump_lval_next {op : UnOp} {st lv st' lv'}
    (h : stepLVal st lv = .next st' lv') :
    stepExpr st (.bump op lv) = .next st' (.bump op lv') := by
  cases lv with
  | target target => simp [stepLVal] at h
  | var name =>
      change
        (match stepLVal st (.var name) with
        | LValOutcome.next stx lvx => ExprOutcome.next stx (.bump op lvx)
        | LValOutcome.target stx target => ExprOutcome.next stx (.bump op (.target target))
        | LValOutcome.runtimeError stx msg => ExprOutcome.runtimeError stx msg) =
          ExprOutcome.next st' (.bump op lv')
      rw [h]
  | special v =>
      change
        (match stepLVal st (.special v) with
        | LValOutcome.next stx lvx => ExprOutcome.next stx (.bump op lvx)
        | LValOutcome.target stx target => ExprOutcome.next stx (.bump op (.target target))
        | LValOutcome.runtimeError stx msg => ExprOutcome.runtimeError stx msg) =
          ExprOutcome.next st' (.bump op lv')
      rw [h]
  | array name index =>
      change
        (match stepLVal st (.array name index) with
        | LValOutcome.next stx lvx => ExprOutcome.next stx (.bump op lvx)
        | LValOutcome.target stx target => ExprOutcome.next stx (.bump op (.target target))
        | LValOutcome.runtimeError stx msg => ExprOutcome.runtimeError stx msg) =
          ExprOutcome.next st' (.bump op lv')
      rw [h]

theorem stepExpr_bump_lval_error {op : UnOp} {st lv st' msg}
    (h : stepLVal st lv = .runtimeError st' msg) :
    stepExpr st (.bump op lv) = .runtimeError st' msg := by
  cases lv with
  | target target => simp [stepLVal] at h
  | var name =>
      change
        (match stepLVal st (.var name) with
        | LValOutcome.next stx lvx => ExprOutcome.next stx (.bump op lvx)
        | LValOutcome.target stx target => ExprOutcome.next stx (.bump op (.target target))
        | LValOutcome.runtimeError stx msg => ExprOutcome.runtimeError stx msg) =
          ExprOutcome.runtimeError st' msg
      rw [h]
  | special v =>
      change
        (match stepLVal st (.special v) with
        | LValOutcome.next stx lvx => ExprOutcome.next stx (.bump op lvx)
        | LValOutcome.target stx target => ExprOutcome.next stx (.bump op (.target target))
        | LValOutcome.runtimeError stx msg => ExprOutcome.runtimeError stx msg) =
          ExprOutcome.runtimeError st' msg
      rw [h]
  | array name index =>
      change
        (match stepLVal st (.array name index) with
        | LValOutcome.next stx lvx => ExprOutcome.next stx (.bump op lvx)
        | LValOutcome.target stx target => ExprOutcome.next stx (.bump op (.target target))
        | LValOutcome.runtimeError stx msg => ExprOutcome.runtimeError stx msg) =
          ExprOutcome.runtimeError st' msg
      rw [h]

private theorem ExprRuns.badBump {st op arg} :
    ExprRuns st (.badBump op arg)
      (.runtimeError st "increment/decrement operand is not an lvalue") := by
  exact ExprRuns.runtimeError (by simp [stepExpr])

private def bumpEvalResult (op : UnOp) (st : RuntimeState) (target : LValueTarget) :
    EvalResult Num :=
  let (stBumped, old, newValue) :=
    bumpLValueTarget st target (op == .preIncr || op == .postIncr)
  match op with
  | .preIncr | .preDecr => .ok stBumped newValue
  | .postIncr | .postDecr => .ok stBumped old
  | .neg => .ok stBumped newValue

private def bumpExprOutcome (op : UnOp) (st : RuntimeState) (target : LValueTarget) :
    ExprOutcome :=
  let (stBumped, old, newValue) :=
    bumpLValueTarget st target (op == .preIncr || op == .postIncr)
  let value :=
    match op with
    | .preIncr | .preDecr => newValue
    | .postIncr | .postDecr => old
    | .neg => newValue
  .value stBumped value

private theorem evalToExprOutcome_bumpEvalResult (op st target) :
    evalToExprOutcome (bumpEvalResult op st target) = bumpExprOutcome op st target := by
  cases op <;> simp [bumpEvalResult, bumpExprOutcome, evalToExprOutcome]

private theorem ExprRuns.bump_target {st op target} :
    ExprRuns st (.bump op (.target target)) (bumpExprOutcome op st target) := by
  cases op <;> simp [bumpExprOutcome]
  all_goals exact ExprRuns.next (by simp [stepExpr]) ExprRuns.value

private theorem evalLValueTarget_ne_control_aux {fuel st lv st' c} :
    evalLValueTarget fuel st lv ≠ .control st' c := by
  induction fuel generalizing st lv with
  | zero =>
      simp [evalLValueTarget]
  | succ fuel' ih =>
      cases lv with
      | var name => simp [evalLValueTarget]
      | special v => simp [evalLValueTarget]
      | array name idx =>
          simp only [evalLValueTarget]
          cases hidx : evalExpr fuel' st idx <;> simp
          next state value =>
            cases hindex : indexOfNum? value <;> simp

private theorem unaryBump_from_eval {fuel' op st arg r}
    (prev : ForwardProps fuel')
    (heval : evalUnary (fuel' + 1) st op arg =
      match lvalOfExpr? arg with
      | none => .runtimeError st "increment/decrement operand is not an lvalue"
      | some lv =>
          match evalLValueTarget fuel' st lv with
          | .ok st target =>
              bumpEvalResult op st target
          | .control st control => .control st control
          | .outOfFuel st => .outOfFuel st
          | .runtimeError st msg => .runtimeError st msg)
    (htermNone : lvalOfExpr? arg = none →
      ExprTerm.ofExpr (.unary op arg) = .badBump op (ExprTerm.ofExpr arg))
    (htermSome : ∀ lv, lvalOfExpr? arg = some lv →
      ExprTerm.ofExpr (.unary op arg) = .bump op (LValTerm.ofLVal lv))
    (h : evalUnary (fuel' + 1) st op arg = r) (hnf : EvalResultNotFuel r) :
    ExprRuns st (ExprTerm.ofExpr (.unary op arg)) (evalToExprOutcome r) := by
  rw [heval] at h
  match hlv : lvalOfExpr? arg with
  | none =>
      have hr : r = .runtimeError st "increment/decrement operand is not an lvalue" := by
        simpa [hlv] using h.symm
      cases hr
      rw [htermNone hlv]
      exact ExprRuns.badBump
  | some lv =>
      rw [htermSome lv hlv]
      match htarget : evalLValueTarget fuel' st lv with
      | .ok st' target =>
          have hr : r = bumpEvalResult op st' target := by
            simpa [hlv, htarget, bumpEvalResult] using h.symm
          cases hr
          have htargetRun := prev.lval st lv (.ok st' target) htarget
            (by simp [EvalResultNotFuel])
          exact LValRuns.lift_target_to_expr
            (k := fun lv => .bump op lv)
            (by intro st lv st' lv' hstep; exact stepExpr_bump_lval_next hstep)
            htargetRun
            (by
              simpa [evalToExprOutcome_bumpEvalResult] using
                (ExprRuns.bump_target (st := st') (op := op) (target := target)))
      | .control st' c =>
          exact False.elim (evalLValueTarget_ne_control_aux (fuel := fuel') (st := st)
            (lv := lv) (st' := st') (c := c) htarget)
      | .outOfFuel st' =>
          have hr : r = .outOfFuel st' := by simpa [hlv, htarget] using h.symm
          cases hr
          cases hnf
      | .runtimeError st' msg =>
          have hr : r = .runtimeError st' msg := by simpa [hlv, htarget] using h.symm
          cases hr
          have htargetRun := prev.lval st lv (.runtimeError st' msg) htarget
            (by simp [EvalResultNotFuel])
          exact LValRuns.lift_error_to_expr
            (k := fun lv => .bump op lv)
            (by intro st lv st' lv' hstep; exact stepExpr_bump_lval_next hstep)
            (by intro st lv st' msg hstep; exact stepExpr_bump_lval_error hstep)
            htargetRun

private theorem evalLValueTarget_ne_control {fuel st lv st' c} :
    evalLValueTarget fuel st lv ≠ .control st' c := by
  induction fuel generalizing st lv with
  | zero =>
      simp [evalLValueTarget]
  | succ fuel' ih =>
      cases lv with
      | var name => simp [evalLValueTarget]
      | special v => simp [evalLValueTarget]
      | array name idx =>
          simp only [evalLValueTarget]
          cases hidx : evalExpr fuel' st idx <;> simp
          next state value =>
            cases hindex : indexOfNum? value <;> simp

theorem stepExpr_bin_rhs_control {op : BinOp} {left : Num}
    {st rhs st' c} (h : stepExpr st rhs = .control st' c) :
    stepExpr st (.bin op (.value left) rhs) = .control st' c := by
  cases rhs <;> simp_all [stepExpr]

theorem stepExpr_bin_rhs_error {op : BinOp} {left : Num}
    {st rhs st' msg} (h : stepExpr st rhs = .runtimeError st' msg) :
    stepExpr st (.bin op (.value left) rhs) = .runtimeError st' msg := by
  cases rhs <;> simp_all [stepExpr]

theorem stepExpr_rel_first_next {rest : List (RelOp × ExprTerm)}
    {st first st' first'} (h : stepExpr st first = .next st' first') :
    stepExpr st (.rel first rest) = .next st' (.rel first' rest) := by
  cases first <;> simp_all [stepExpr]
  all_goals first | rfl | (rcases h with ⟨hst, he⟩; subst hst; subst he; rfl)

theorem stepExpr_rel_first_control {rest : List (RelOp × ExprTerm)}
    {st first st' c} (h : stepExpr st first = .control st' c) :
    stepExpr st (.rel first rest) = .control st' c := by
  cases first <;> simp_all [stepExpr]

theorem stepExpr_rel_first_error {rest : List (RelOp × ExprTerm)}
    {st first st' msg} (h : stepExpr st first = .runtimeError st' msg) :
    stepExpr st (.rel first rest) = .runtimeError st' msg := by
  cases first <;> simp_all [stepExpr]

theorem stepExpr_rel_rhs_next {left : Num} {op : RelOp}
    {tail : List (RelOp × ExprTerm)} {st rhs st' rhs'}
    (h : stepExpr st rhs = .next st' rhs') :
    stepExpr st (.rel (.value left) ((op, rhs) :: tail)) =
      .next st' (.rel (.value left) ((op, rhs') :: tail)) := by
  cases rhs <;> simp_all [stepExpr]
  all_goals first | rfl | (rcases h with ⟨hst, he⟩; subst hst; subst he; rfl)

theorem stepExpr_rel_rhs_control {left : Num} {op : RelOp}
    {tail : List (RelOp × ExprTerm)} {st rhs st' c}
    (h : stepExpr st rhs = .control st' c) :
    stepExpr st (.rel (.value left) ((op, rhs) :: tail)) = .control st' c := by
  cases rhs <;> simp_all [stepExpr]

theorem stepExpr_rel_rhs_error {left : Num} {op : RelOp}
    {tail : List (RelOp × ExprTerm)} {st rhs st' msg}
    (h : stepExpr st rhs = .runtimeError st' msg) :
    stepExpr st (.rel (.value left) ((op, rhs) :: tail)) = .runtimeError st' msg := by
  cases rhs <;> simp_all [stepExpr]

private theorem ExprRuns.rel_nil {st left} :
    ExprRuns st (.rel (.value left) []) (.value st left) := by
  exact ExprRuns.next (by simp [stepExpr]) ExprRuns.value

private theorem ExprRuns.rel_value_cons {st left op right tail o}
    (hcont :
      ExprRuns st
        (match tail with
        | [] => .value (boolNum (applyRel op left right))
        | _ => .rel (.value (boolNum (applyRel op left right))) tail)
        o) :
    ExprRuns st (.rel (.value left) ((op, .value right) :: tail)) o := by
  exact ExprRuns.next (by cases tail <;> simp [stepExpr]) hcont

private theorem LValRuns.array_value_ok {st name idxNum idx}
    (h : indexOfNum? idxNum = .ok idx) :
    LValRuns st (.array name (.value idxNum))
      (.target (ensureArrayId st name).1 (.arrayElem (ensureArrayId st name).2 idx)) := by
  exact LValRuns.next (by simp [stepLVal, h]) LValRuns.target

private theorem LValRuns.array_value_error {st name idxNum msg}
    (h : indexOfNum? idxNum = .error msg) :
    LValRuns st (.array name (.value idxNum)) (.runtimeError st msg) := by
  exact LValRuns.runtimeError (by simp [stepLVal, h])

theorem stepArgs_expr_head_next {rest : List ArgTerm} {st e st' e'}
    (h : stepExpr st e = .next st' e') :
    stepArgs st (.expr e :: rest) = .next st' (.expr e' :: rest) := by
  cases e <;> simp_all [stepArgs, stepExpr]
  all_goals first | rfl | (rcases h with ⟨hst, he⟩; subst hst; subst he; rfl)

theorem stepArgs_expr_head_control {rest : List ArgTerm} {st e st' c}
    (h : stepExpr st e = .control st' c) :
    stepArgs st (.expr e :: rest) = .control st' c := by
  cases e <;> simp_all [stepArgs, stepExpr]

theorem stepArgs_expr_head_error {rest : List ArgTerm} {st e st' msg}
    (h : stepExpr st e = .runtimeError st' msg) :
    stepArgs st (.expr e :: rest) = .runtimeError st' msg := by
  cases e <;> simp_all [stepArgs, stepExpr]

theorem stepArgs_expr_value_tail_next {value : Num} {st rest st' rest'}
    (h : stepArgs st rest = .next st' rest') :
    stepArgs st (.expr (.value value) :: rest) = .next st' (.expr (.value value) :: rest') := by
  simp [stepArgs, h]

theorem stepArgs_expr_value_tail_values {value : Num} {st rest st' values}
    (h : stepArgs st rest = .values st' values) :
    stepArgs st (.expr (.value value) :: rest) = .values st' (.inl value :: values) := by
  simp [stepArgs, h]

theorem stepArgs_expr_value_tail_control {value : Num} {st rest st' c}
    (h : stepArgs st rest = .control st' c) :
    stepArgs st (.expr (.value value) :: rest) = .control st' c := by
  simp [stepArgs, h]

theorem stepArgs_expr_value_tail_error {value : Num} {st rest st' msg}
    (h : stepArgs st rest = .runtimeError st' msg) :
    stepArgs st (.expr (.value value) :: rest) = .runtimeError st' msg := by
  simp [stepArgs, h]

theorem stepArgs_arrayRef_tail_next {name : Name} {st rest st' rest'}
    (h : stepArgs st rest = .next st' rest') :
    stepArgs st (.arrayRef name :: rest) = .next st' (.arrayRef name :: rest') := by
  simp [stepArgs, h]

theorem stepArgs_arrayRef_tail_values {name : Name} {st rest st' values}
    (h : stepArgs st rest = .values st' values) :
    stepArgs st (.arrayRef name :: rest) = .values st' (.inr name :: values) := by
  simp [stepArgs, h]

theorem stepArgs_arrayRef_tail_control {name : Name} {st rest st' c}
    (h : stepArgs st rest = .control st' c) :
    stepArgs st (.arrayRef name :: rest) = .control st' c := by
  simp [stepArgs, h]

theorem stepArgs_arrayRef_tail_error {name : Name} {st rest st' msg}
    (h : stepArgs st rest = .runtimeError st' msg) :
    stepArgs st (.arrayRef name :: rest) = .runtimeError st' msg := by
  simp [stepArgs, h]

theorem stepStmt_expr_next {original : Expr} {st e st' e'}
    (h : stepExpr st e = .next st' e') :
    stepStmt st (.expr original e) = .next st' (.expr original e') := by
  cases e <;> simp_all [stepStmt, stepExpr]
  all_goals first | (rcases h with ⟨rfl, rfl⟩; rfl) | rfl

theorem stepStmt_expr_control {original : Expr} {st e st' c}
    (h : stepExpr st e = .control st' c) :
    stepStmt st (.expr original e) = .control st' c := by
  cases e <;> simp_all [stepStmt, stepExpr]

theorem stepStmt_expr_error {original : Expr} {st e st' msg}
    (h : stepExpr st e = .runtimeError st' msg) :
    stepStmt st (.expr original e) = .runtimeError st' msg := by
  cases e <;> simp_all [stepStmt, stepExpr]

theorem stepStmt_eval_next {st e st' e'}
    (h : stepExpr st e = .next st' e') :
    stepStmt st (.eval e) = .next st' (.eval e') := by
  cases e <;> simp_all [stepStmt, stepExpr]
  all_goals first | (rcases h with ⟨rfl, rfl⟩; rfl) | rfl

theorem stepStmt_eval_control {st e st' c}
    (h : stepExpr st e = .control st' c) :
    stepStmt st (.eval e) = .control st' c := by
  cases e <;> simp_all [stepStmt, stepExpr]

theorem stepStmt_eval_error {st e st' msg}
    (h : stepExpr st e = .runtimeError st' msg) :
    stepStmt st (.eval e) = .runtimeError st' msg := by
  cases e <;> simp_all [stepStmt, stepExpr]

theorem stepStmt_if_next {branch : StmtTerm} {st e st' e'}
    (h : stepExpr st e = .next st' e') :
    stepStmt st (.ifThen e branch) = .next st' (.ifThen e' branch) := by
  cases e <;> simp_all [stepStmt, stepExpr]
  all_goals first | (rcases h with ⟨rfl, rfl⟩; rfl) | rfl

theorem stepStmt_if_control {branch : StmtTerm} {st e st' c}
    (h : stepExpr st e = .control st' c) :
    stepStmt st (.ifThen e branch) = .control st' c := by
  cases e <;> simp_all [stepStmt, stepExpr]

theorem stepStmt_if_error {branch : StmtTerm} {st e st' msg}
    (h : stepExpr st e = .runtimeError st' msg) :
    stepStmt st (.ifThen e branch) = .runtimeError st' msg := by
  cases e <;> simp_all [stepStmt, stepExpr]

theorem stepStmt_while_next {source : Expr} {body : StmtTerm} {st e st' e'}
    (h : stepExpr st e = .next st' e') :
    stepStmt st (.while source e body) = .next st' (.while source e' body) := by
  cases e <;> simp_all [stepStmt, stepExpr]
  all_goals first | (rcases h with ⟨rfl, rfl⟩; rfl) | rfl

theorem stepStmt_while_control {source : Expr} {body : StmtTerm} {st e st' c}
    (h : stepExpr st e = .control st' c) :
    stepStmt st (.while source e body) = .control st' c := by
  cases e <;> simp_all [stepStmt, stepExpr]

theorem stepStmt_while_error {source : Expr} {body : StmtTerm} {st e st' msg}
    (h : stepExpr st e = .runtimeError st' msg) :
    stepStmt st (.while source e body) = .runtimeError st' msg := by
  cases e <;> simp_all [stepStmt, stepExpr]

theorem stepStmt_forCheck_next {source update : Expr} {body : StmtTerm} {st e st' e'}
    (h : stepExpr st e = .next st' e') :
    stepStmt st (.forCheck source e update body) =
      .next st' (.forCheck source e' update body) := by
  cases e <;> simp_all [stepStmt, stepExpr]
  all_goals first | (rcases h with ⟨rfl, rfl⟩; rfl) | rfl

theorem stepStmt_forCheck_control {source update : Expr} {body : StmtTerm} {st e st' c}
    (h : stepExpr st e = .control st' c) :
    stepStmt st (.forCheck source e update body) = .control st' c := by
  cases e <;> simp_all [stepStmt, stepExpr]

theorem stepStmt_forCheck_error {source update : Expr} {body : StmtTerm} {st e st' msg}
    (h : stepExpr st e = .runtimeError st' msg) :
    stepStmt st (.forCheck source e update body) = .runtimeError st' msg := by
  cases e <;> simp_all [stepStmt, stepExpr]

theorem stepStmt_forUpdate_next {source updateSource : Expr} {body : StmtTerm}
    {st e st' e'} (h : stepExpr st e = .next st' e') :
    stepStmt st (.forUpdate source updateSource e body) =
      .next st' (.forUpdate source updateSource e' body) := by
  cases e <;> simp_all [stepStmt, stepExpr]
  all_goals first | (rcases h with ⟨rfl, rfl⟩; rfl) | rfl

theorem stepStmt_forUpdate_control {source updateSource : Expr} {body : StmtTerm}
    {st e st' c} (h : stepExpr st e = .control st' c) :
    stepStmt st (.forUpdate source updateSource e body) = .control st' c := by
  cases e <;> simp_all [stepStmt, stepExpr]

theorem stepStmt_forUpdate_error {source updateSource : Expr} {body : StmtTerm}
    {st e st' msg} (h : stepExpr st e = .runtimeError st' msg) :
    stepStmt st (.forUpdate source updateSource e body) = .runtimeError st' msg := by
  cases e <;> simp_all [stepStmt, stepExpr]

theorem stepStmt_return_next {st e st' e'}
    (h : stepExpr st e = .next st' e') :
    stepStmt st (.return (some e)) = .next st' (.return (some e')) := by
  cases e <;> simp_all [stepStmt, stepExpr]
  all_goals first | (rcases h with ⟨rfl, rfl⟩; rfl) | rfl

theorem stepStmt_return_control {st e st' c}
    (h : stepExpr st e = .control st' c) :
    stepStmt st (.return (some e)) = .control st' c := by
  cases e <;> simp_all [stepStmt, stepExpr]

theorem stepStmt_return_error {st e st' msg}
    (h : stepExpr st e = .runtimeError st' msg) :
    stepStmt st (.return (some e)) = .runtimeError st' msg := by
  cases e <;> simp_all [stepStmt, stepExpr]

attribute [local simp] lookupFunction_ensureArrayId lookupFunction_writeLValueTarget
  lookupFunction_bumpLValueTarget lookupFunction_appendOutput lookupFunction_printNumLine

private def ExprOutcomeLookup (name : Name) (st : RuntimeState) : ExprOutcome → Prop
  | .next st' _ => lookupFunction st' name = lookupFunction st name
  | .value st' _ => lookupFunction st' name = lookupFunction st name
  | .control st' _ => lookupFunction st' name = lookupFunction st name
  | .runtimeError st' _ => lookupFunction st' name = lookupFunction st name

private def LValOutcomeLookup (name : Name) (st : RuntimeState) : LValOutcome → Prop
  | .next st' _ => lookupFunction st' name = lookupFunction st name
  | .target st' _ => lookupFunction st' name = lookupFunction st name
  | .runtimeError st' _ => lookupFunction st' name = lookupFunction st name

private def ArgsOutcomeLookup (name : Name) (st : RuntimeState) : ArgListOutcome → Prop
  | .next st' _ => lookupFunction st' name = lookupFunction st name
  | .values st' _ => lookupFunction st' name = lookupFunction st name
  | .control st' _ => lookupFunction st' name = lookupFunction st name
  | .runtimeError st' _ => lookupFunction st' name = lookupFunction st name

private def StmtOutcomeLookup (name : Name) (st : RuntimeState) : StmtOutcome → Prop
  | .next st' _ => lookupFunction st' name = lookupFunction st name
  | .done st' => lookupFunction st' name = lookupFunction st name
  | .control st' _ => lookupFunction st' name = lookupFunction st name
  | .runtimeError st' _ => lookupFunction st' name = lookupFunction st name

private def BodyOutcomeLookup (name : Name) (st : RuntimeState) : BodyOutcome → Prop
  | .next st' _ => lookupFunction st' name = lookupFunction st name
  | .done st' => lookupFunction st' name = lookupFunction st name
  | .control st' _ => lookupFunction st' name = lookupFunction st name
  | .runtimeError st' _ => lookupFunction st' name = lookupFunction st name

private theorem enterFunction_lookupFunction {st : RuntimeState} {defn : FunDef}
    {argValues : List (Sum Num Name)} {o : ExprOutcome} {name : Name}
    (h : enterFunction st defn argValues = o) :
    ExprOutcomeLookup name st o := by
  unfold enterFunction at h
  simp only at h
  cases hbind :
      bindParams ({ st with frames := { constBase := st.ibase } :: st.frames })
        defn.params argValues with
  | ok st' =>
      simp [hbind] at h
      cases h
      exact
        calc
          lookupFunction (bindAutoDecls st' (collectAutos defn.body)) name
              = lookupFunction st' name := lookupFunction_bindAutoDecls _ _ _
          _ = lookupFunction ({ st with frames := { constBase := st.ibase } :: st.frames }) name :=
              bindParams_lookupFunction hbind
          _ = lookupFunction st name := rfl
  | error msg =>
      simp [hbind] at h
      cases h
      rfl

attribute [local simp] enterFunction_lookupFunction

private theorem lookupFunction_ensureArrayId_eq {st st' : RuntimeState} {arrayName name : Name}
    {id : ArrayId} (h : ensureArrayId st arrayName = (st', id)) :
    lookupFunction st' name = lookupFunction st name := by
  simpa [h] using (lookupFunction_ensureArrayId st arrayName name)

attribute [local simp] lookupFunction_ensureArrayId_eq

private theorem liftAE_call_lookupFunction {name fname : Name} {defn : FunDef} {st o}
    (h : ArgsOutcomeLookup name st o) :
    ExprOutcomeLookup name st
      (liftAE (fun a => ExprTerm.call fname a) (fun st vs => enterFunction st defn vs) o) := by
  cases o <;> simp [ArgsOutcomeLookup, ExprOutcomeLookup, liftAE] at h ⊢
  case next => exact h
  case control => exact h
  case runtimeError => exact h
  case values st' values =>
    cases henter : enterFunction st' defn values <;>
      have hpres := enterFunction_lookupFunction (name := name) henter <;>
      simp [ExprOutcomeLookup] at hpres ⊢ <;> exact hpres.trans h

private theorem liftActiveCall_lookupFunction {name : Name} {st o}
    (h : BodyOutcomeLookup name st o) : ExprOutcomeLookup name st (liftActiveCall o) := by
  cases o <;> simp [BodyOutcomeLookup, ExprOutcomeLookup, liftActiveCall, popFrame] at h ⊢
  case next => exact h
  case done => simpa [lookupFunction, popFrame] using h
  case runtimeError => simpa [lookupFunction, popFrame] using h
  case control state control => cases control <;> simpa [lookupFunction, popFrame] using h

private theorem liftLoopBody_lookupFunction {name : Name} {st after o}
    (h : StmtOutcomeLookup name st o) : StmtOutcomeLookup name st (liftLoopBody after o) := by
  cases o <;> simp [StmtOutcomeLookup, liftLoopBody] at h ⊢
  case next => exact h
  case done => exact h
  case runtimeError => exact h
  case control state control => cases control <;> simpa using h

local macro "lookup_ss" : tactic =>
  `(tactic| simp_all [ExprOutcomeLookup, LValOutcomeLookup, ArgsOutcomeLookup,
    StmtOutcomeLookup, BodyOutcomeLookup, liftE, liftLE, liftAE, liftActiveCall,
    liftIndexLVal, liftArgsTail, liftExprArgs, liftExprStmt, liftLoopBody, liftSeq,
    liftBlock, liftBodyStep, bumpOutcome, popFrame])

local macro "outcome_cases" : tactic =>
  `(tactic| first
    | lookup_ss; done
    | exact lookupFunction_ensureArrayId_eq (by assumption)
    | exact liftAE_call_lookupFunction (by assumption)
    | exact liftActiveCall_lookupFunction (by assumption)
    | exact liftLoopBody_lookupFunction (by assumption)
    | (cases ‹ExprOutcome› <;> first | lookup_ss; done | assumption | rfl)
    | (cases ‹LValOutcome› <;> first | lookup_ss; done | assumption | rfl)
    | (cases ‹ArgListOutcome› <;> first | lookup_ss; done | assumption | rfl)
    | (cases ‹StmtOutcome› <;> first | lookup_ss; done | assumption | rfl)
    | (cases ‹BodyOutcome› <;> first | lookup_ss; done | assumption | rfl)
    | assumption
    | rfl)

theorem stepExprRel_lookupFunction (name : Name) (st : RuntimeState) :
    ∀ {e o}, StepExpr st e o → ExprOutcomeLookup name st o := by
  apply @StepExpr.rec st
    (motive_1 := fun _ o _ => ExprOutcomeLookup name st o)
    (motive_2 := fun _ o _ => LValOutcomeLookup name st o)
    (motive_3 := fun _ o _ => ArgsOutcomeLookup name st o)
    (motive_4 := fun _ o _ => StmtOutcomeLookup name st o)
    (motive_5 := fun _ o _ => BodyOutcomeLookup name st o)
  all_goals (intros; outcome_cases)

theorem stepLValRel_lookupFunction (name : Name) (st : RuntimeState) :
    ∀ {lv o}, StepLVal st lv o → LValOutcomeLookup name st o := by
  apply @StepLVal.rec st
    (motive_1 := fun _ o _ => ExprOutcomeLookup name st o)
    (motive_2 := fun _ o _ => LValOutcomeLookup name st o)
    (motive_3 := fun _ o _ => ArgsOutcomeLookup name st o)
    (motive_4 := fun _ o _ => StmtOutcomeLookup name st o)
    (motive_5 := fun _ o _ => BodyOutcomeLookup name st o)
  all_goals (intros; outcome_cases)

theorem stepArgsRel_lookupFunction (name : Name) (st : RuntimeState) :
    ∀ {args o}, StepArgs st args o → ArgsOutcomeLookup name st o := by
  apply @StepArgs.rec st
    (motive_1 := fun _ o _ => ExprOutcomeLookup name st o)
    (motive_2 := fun _ o _ => LValOutcomeLookup name st o)
    (motive_3 := fun _ o _ => ArgsOutcomeLookup name st o)
    (motive_4 := fun _ o _ => StmtOutcomeLookup name st o)
    (motive_5 := fun _ o _ => BodyOutcomeLookup name st o)
  all_goals (intros; outcome_cases)

theorem stepStmtRel_lookupFunction (name : Name) (st : RuntimeState) :
    ∀ {stmt o}, StepStmt st stmt o → StmtOutcomeLookup name st o := by
  apply @StepStmt.rec st
    (motive_1 := fun _ o _ => ExprOutcomeLookup name st o)
    (motive_2 := fun _ o _ => LValOutcomeLookup name st o)
    (motive_3 := fun _ o _ => ArgsOutcomeLookup name st o)
    (motive_4 := fun _ o _ => StmtOutcomeLookup name st o)
    (motive_5 := fun _ o _ => BodyOutcomeLookup name st o)
  all_goals (intros; outcome_cases)

theorem stepBodyRel_lookupFunction (name : Name) (st : RuntimeState) :
    ∀ {body o}, StepBody st body o → BodyOutcomeLookup name st o := by
  apply @StepBody.rec st
    (motive_1 := fun _ o _ => ExprOutcomeLookup name st o)
    (motive_2 := fun _ o _ => LValOutcomeLookup name st o)
    (motive_3 := fun _ o _ => ArgsOutcomeLookup name st o)
    (motive_4 := fun _ o _ => StmtOutcomeLookup name st o)
    (motive_5 := fun _ o _ => BodyOutcomeLookup name st o)
  all_goals (intros; outcome_cases)

theorem stepExpr_lookupFunction (name : Name) {st e o}
    (h : stepExpr st e = o) : ExprOutcomeLookup name st o := by
  by_cases hv : ExprTerm.isValue e = false
  · have hrel := stepExprRel_lookupFunction name st (stepExpr_complete (st := st) (e := e) hv)
    simpa [h] using hrel
  · cases e <;> simp [ExprTerm.isValue] at hv
    simp [stepExpr] at h
    cases h
    simp [ExprOutcomeLookup]

theorem stepLVal_lookupFunction (name : Name) {st lv o}
    (h : stepLVal st lv = o) : LValOutcomeLookup name st o := by
  by_cases hv : LValTerm.isTarget lv = false
  · have hrel := stepLValRel_lookupFunction name st
      (stepLVal_complete (st := st) (lv := lv) hv)
    simpa [h] using hrel
  · cases lv <;> simp [LValTerm.isTarget] at hv
    simp [stepLVal] at h
    cases h
    simp [LValOutcomeLookup]

theorem stepArgs_lookupFunction (name : Name) {st args o}
    (h : stepArgs st args = o) : ArgsOutcomeLookup name st o := by
  have hrel := stepArgsRel_lookupFunction name st (stepArgs_complete (st := st) (a := args))
  simpa [h] using hrel

theorem stepStmt_lookupFunction (name : Name) {st stmt o}
    (h : stepStmt st stmt = o) : StmtOutcomeLookup name st o := by
  have hrel := stepStmtRel_lookupFunction name st (stepStmt_complete (st := st) (s := stmt))
  simpa [h] using hrel

theorem stepBody_lookupFunction (name : Name) {st body o}
    (h : stepBody st body = o) : BodyOutcomeLookup name st o := by
  have hrel := stepBodyRel_lookupFunction name st (stepBody_complete (st := st) (b := body))
  simpa [h] using hrel

private def ExprOutcomeNoNormal : ExprOutcome → Prop
  | .control _ c => c ≠ .normal
  | _ => True

private def LValOutcomeNoNormal : LValOutcome → Prop
  | _ => True

private def ArgsOutcomeNoNormal : ArgListOutcome → Prop
  | .control _ c => c ≠ .normal
  | _ => True

private def StmtOutcomeNoNormal : StmtOutcome → Prop
  | .control _ c => c ≠ .normal
  | _ => True

private def BodyOutcomeNoNormal : BodyOutcome → Prop
  | .control _ c => c ≠ .normal
  | _ => True

private theorem control_break_ne_normal : Control.break ≠ Control.normal := by
  intro h
  cases h

private theorem control_return_ne_normal (value? : Option Num) :
    Control.return value? ≠ Control.normal := by
  intro h
  cases h

private theorem control_quit_ne_normal : Control.quit ≠ Control.normal := by
  intro h
  cases h

attribute [local simp] control_break_ne_normal control_return_ne_normal control_quit_ne_normal

private theorem liftE_noNormal {k : ExprTerm → ExprTerm} {o : ExprOutcome}
    (h : ExprOutcomeNoNormal o) : ExprOutcomeNoNormal (liftE k o) := by
  cases o <;> simp [ExprOutcomeNoNormal, liftE] at h ⊢
  case control state control => cases control <;> simp at h ⊢

private theorem liftLE_noNormal {kn : LValTerm → ExprTerm}
    {kt : RuntimeState → LValueTarget → ExprOutcome} {o : LValOutcome}
    (ht : ∀ st target, ExprOutcomeNoNormal (kt st target)) :
    ExprOutcomeNoNormal (liftLE kn kt o) := by
  cases o <;> simp [ExprOutcomeNoNormal, liftLE]
  case target state target => exact ht state target

private theorem enterFunction_noNormal {st : RuntimeState} {defn : FunDef}
    {argValues : List (Sum Num Name)} : ExprOutcomeNoNormal (enterFunction st defn argValues) := by
  unfold enterFunction
  cases hbind : bindParams ({ st with frames := { constBase := st.ibase } :: st.frames })
      defn.params argValues <;>
    simp [hbind, ExprOutcomeNoNormal]

private theorem liftAE_noNormal {kn : List ArgTerm → ExprTerm}
    {kv : RuntimeState → List (Sum Num Name) → ExprOutcome} {o : ArgListOutcome}
    (hv : ∀ st values, ExprOutcomeNoNormal (kv st values))
    (h : ArgsOutcomeNoNormal o) : ExprOutcomeNoNormal (liftAE kn kv o) := by
  cases o <;> simp [ArgsOutcomeNoNormal, ExprOutcomeNoNormal, liftAE] at h ⊢
  case values state values => exact hv state values
  case control state control =>
    cases control <;> simp at h ⊢
    all_goals (intro hc; cases hc)

private theorem liftActiveCall_noNormal {o : BodyOutcome}
    (h : BodyOutcomeNoNormal o) : ExprOutcomeNoNormal (liftActiveCall o) := by
  cases o <;> simp [BodyOutcomeNoNormal, ExprOutcomeNoNormal, liftActiveCall] at h ⊢
  case control state control => cases control <;> simp at h ⊢

private theorem liftArgsTail_noNormal {kn : List ArgTerm → List ArgTerm}
    {kv : List (Sum Num Name) → List (Sum Num Name)} {o : ArgListOutcome}
    (h : ArgsOutcomeNoNormal o) : ArgsOutcomeNoNormal (liftArgsTail kn kv o) := by
  cases o <;> simp [ArgsOutcomeNoNormal, liftArgsTail] at h ⊢
  case control state control => cases control <;> simp at h ⊢

private theorem liftExprArgs_noNormal {kn : ExprTerm → List ArgTerm} {o : ExprOutcome}
    (h : ExprOutcomeNoNormal o) : ArgsOutcomeNoNormal (liftExprArgs kn o) := by
  cases o <;> simp [ExprOutcomeNoNormal, ArgsOutcomeNoNormal, liftExprArgs] at h ⊢
  case control state control =>
    cases control <;> simp at h ⊢
    all_goals (intro hc; cases hc)

private theorem liftExprStmt_noNormal {k : ExprTerm → StmtTerm} {o : ExprOutcome}
    (h : ExprOutcomeNoNormal o) : StmtOutcomeNoNormal (liftExprStmt k o) := by
  cases o <;> simp [ExprOutcomeNoNormal, StmtOutcomeNoNormal, liftExprStmt] at h ⊢
  case control state control =>
    cases control <;> simp at h ⊢
    all_goals (intro hc; cases hc)

private theorem liftLoopBody_noNormal {after : StmtTerm} {o : StmtOutcome}
    (h : StmtOutcomeNoNormal o) : StmtOutcomeNoNormal (liftLoopBody after o) := by
  cases o <;> simp [StmtOutcomeNoNormal, liftLoopBody] at h ⊢
  case control state control => cases control <;> simp at h ⊢

private theorem liftSeq_noNormal {second : StmtTerm} {o : StmtOutcome}
    (h : StmtOutcomeNoNormal o) : StmtOutcomeNoNormal (liftSeq second o) := by
  cases o <;> simp [StmtOutcomeNoNormal, liftSeq] at h ⊢
  case control state control =>
    cases control <;> simp at h ⊢
    all_goals (intro hc; cases hc)

private theorem liftBlock_noNormal {o : BodyOutcome}
    (h : BodyOutcomeNoNormal o) : StmtOutcomeNoNormal (liftBlock o) := by
  cases o <;> simp [BodyOutcomeNoNormal, StmtOutcomeNoNormal, liftBlock] at h ⊢
  case control state control =>
    cases control <;> simp at h ⊢
    all_goals (intro hc; cases hc)

private theorem liftBodyStep_noNormal {rest : List StmtTerm} {o : StmtOutcome}
    (h : StmtOutcomeNoNormal o) : BodyOutcomeNoNormal (liftBodyStep rest o) := by
  cases o <;> simp [StmtOutcomeNoNormal, BodyOutcomeNoNormal, liftBodyStep] at h ⊢
  case control state control =>
    cases control <;> simp at h ⊢
    all_goals (intro hc; cases hc)

local macro "normal_ss" : tactic =>
  `(tactic| simp_all [ExprOutcomeNoNormal, LValOutcomeNoNormal, ArgsOutcomeNoNormal,
    StmtOutcomeNoNormal, BodyOutcomeNoNormal, liftE, liftLE, liftAE, liftActiveCall,
    liftIndexLVal, liftArgsTail, liftExprArgs, liftExprStmt, liftLoopBody, liftSeq,
    liftBlock, liftBodyStep, bumpOutcome, enterFunction])

local macro "normal_cases" : tactic =>
  `(tactic| first
    | normal_ss; done
    | (cases ‹Control› <;> normal_ss; done)
    | (cases ‹ExprOutcome› <;> try cases ‹Control› <;> (normal_ss; done))
    | (cases ‹LValOutcome› <;> (normal_ss; done))
    | (cases ‹ArgListOutcome› <;> try cases ‹Control› <;> (normal_ss; done))
    | (cases ‹StmtOutcome› <;> try cases ‹Control› <;> (normal_ss; done))
    | (cases ‹BodyOutcome› <;> try cases ‹Control› <;> (normal_ss; done)))

theorem stepExprRel_noNormal (st : RuntimeState) :
    ∀ {e o}, StepExpr st e o → ExprOutcomeNoNormal o := by
  apply @StepExpr.rec st
    (motive_1 := fun _ o _ => ExprOutcomeNoNormal o)
    (motive_2 := fun _ o _ => LValOutcomeNoNormal o)
    (motive_3 := fun _ o _ => ArgsOutcomeNoNormal o)
    (motive_4 := fun _ o _ => StmtOutcomeNoNormal o)
    (motive_5 := fun _ o _ => BodyOutcomeNoNormal o)
  all_goals
    intros
    first
    | exact liftE_noNormal (by assumption)
    | exact liftLE_noNormal (by intro st target; simp [ExprOutcomeNoNormal])
    | exact liftAE_noNormal
        (by intro st values; exact enterFunction_noNormal) (by assumption)
    | exact liftActiveCall_noNormal (by assumption)
    | exact liftArgsTail_noNormal (by assumption)
    | exact liftExprArgs_noNormal (by assumption)
    | exact liftExprStmt_noNormal (by assumption)
    | exact liftLoopBody_noNormal (by assumption)
    | exact liftSeq_noNormal (by assumption)
    | exact liftBlock_noNormal (by assumption)
    | exact liftBodyStep_noNormal (by assumption)
    | normal_cases

theorem stepExpr_no_control_normal {st e st'}
    (h : stepExpr st e = .control st' .normal) : False := by
  by_cases hv : ExprTerm.isValue e = false
  · have hrel := stepExprRel_noNormal st (stepExpr_complete (st := st) (e := e) hv)
    rw [h] at hrel
    exact hrel rfl
  · cases e <;> simp [ExprTerm.isValue] at hv
    simp [stepExpr] at h

private theorem ExprRuns.no_control_normal {st e st'}
    (h : ExprRuns st e (.control st' .normal)) : False := by
  generalize hout : ExprOutcome.control st' Control.normal = out at h
  induction h with
  | value => cases hout
  | control hstep =>
      cases hout
      exact stepExpr_no_control_normal hstep
  | runtimeError _ => cases hout
  | next _ _ ih => exact ih hout

private theorem stepStmtRel_noNormal (st : RuntimeState) :
    ∀ {s o}, StepStmt st s o → StmtOutcomeNoNormal o := by
  apply @StepStmt.rec st
    (motive_1 := fun _ o _ => ExprOutcomeNoNormal o)
    (motive_2 := fun _ o _ => LValOutcomeNoNormal o)
    (motive_3 := fun _ o _ => ArgsOutcomeNoNormal o)
    (motive_4 := fun _ o _ => StmtOutcomeNoNormal o)
    (motive_5 := fun _ o _ => BodyOutcomeNoNormal o)
  all_goals
    intros
    first
    | exact liftE_noNormal (by assumption)
    | exact liftLE_noNormal (by intro st target; simp [ExprOutcomeNoNormal])
    | exact liftAE_noNormal
        (by intro st values; exact enterFunction_noNormal) (by assumption)
    | exact liftActiveCall_noNormal (by assumption)
    | exact liftArgsTail_noNormal (by assumption)
    | exact liftExprArgs_noNormal (by assumption)
    | exact liftExprStmt_noNormal (by assumption)
    | exact liftLoopBody_noNormal (by assumption)
    | exact liftSeq_noNormal (by assumption)
    | exact liftBlock_noNormal (by assumption)
    | exact liftBodyStep_noNormal (by assumption)
    | normal_cases

private theorem stepBodyRel_noNormal (st : RuntimeState) :
    ∀ {b o}, StepBody st b o → BodyOutcomeNoNormal o := by
  apply @StepBody.rec st
    (motive_1 := fun _ o _ => ExprOutcomeNoNormal o)
    (motive_2 := fun _ o _ => LValOutcomeNoNormal o)
    (motive_3 := fun _ o _ => ArgsOutcomeNoNormal o)
    (motive_4 := fun _ o _ => StmtOutcomeNoNormal o)
    (motive_5 := fun _ o _ => BodyOutcomeNoNormal o)
  all_goals
    intros
    first
    | exact liftE_noNormal (by assumption)
    | exact liftLE_noNormal (by intro st target; simp [ExprOutcomeNoNormal])
    | exact liftAE_noNormal
        (by intro st values; exact enterFunction_noNormal) (by assumption)
    | exact liftActiveCall_noNormal (by assumption)
    | exact liftArgsTail_noNormal (by assumption)
    | exact liftExprArgs_noNormal (by assumption)
    | exact liftExprStmt_noNormal (by assumption)
    | exact liftLoopBody_noNormal (by assumption)
    | exact liftSeq_noNormal (by assumption)
    | exact liftBlock_noNormal (by assumption)
    | exact liftBodyStep_noNormal (by assumption)
    | normal_cases

/-- Statement steps never produce the `.normal` control outcome. -/
theorem stepStmt_control_ne_normal {st s st' c}
    (h : stepStmt st s = .control st' c) : c ≠ .normal := by
  have hrel := stepStmtRel_noNormal st (stepStmt_complete (st := st) (s := s))
  rw [h] at hrel
  simpa [StmtOutcomeNoNormal] using hrel

/-- Body steps never produce the `.normal` control outcome. -/
theorem stepBody_control_ne_normal {st b st' c}
    (h : stepBody st b = .control st' c) : c ≠ .normal := by
  have hrel := stepBodyRel_noNormal st (stepBody_complete (st := st) (b := b))
  rw [h] at hrel
  simpa [BodyOutcomeNoNormal] using hrel

private def ExprOutcomeNoValue : ExprOutcome → Prop
  | .value _ _ => False
  | _ => True

private def LValOutcomeNoTarget : LValOutcome → Prop
  | .target _ _ => False
  | _ => True

set_option linter.unusedSimpArgs false in
private theorem stepExprRel_noValue (st : RuntimeState) :
    ∀ {e o}, StepExpr st e o → ExprOutcomeNoValue o := by
  apply @StepExpr.rec st
    (motive_1 := fun _ o _ => ExprOutcomeNoValue o)
    (motive_2 := fun _ o _ => LValOutcomeNoTarget o)
    (motive_3 := fun _ o _ => True)
    (motive_4 := fun _ o _ => True)
    (motive_5 := fun _ o _ => True)
  case callDef =>
    intros
    cases ‹ArgListOutcome›
    case values =>
      simp [liftAE, enterFunction]
      split <;> simp [ExprOutcomeNoValue]
    all_goals simp [liftAE, ExprOutcomeNoValue]
  case activeCall =>
    intros
    cases ‹BodyOutcome› <;> simp [liftActiveCall, ExprOutcomeNoValue]
    cases ‹Control› <;> simp [liftActiveCall, ExprOutcomeNoValue]
  all_goals intros
  all_goals
    first
    | trivial
    | (cases ‹ExprOutcome› <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget, liftE, liftLE, liftAE,
          liftActiveCall, liftIndexLVal, liftArgsTail, liftExprArgs, enterFunction,
          bumpOutcome] <;>
        (repeat' split) <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget])
    | (cases ‹LValOutcome› <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget, liftE, liftLE, liftAE,
          liftActiveCall, liftIndexLVal, liftArgsTail, liftExprArgs, enterFunction,
          bumpOutcome] <;>
        (repeat' split) <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget])
    | (cases ‹ArgListOutcome› <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget, liftE, liftLE, liftAE,
          liftActiveCall, liftIndexLVal, liftArgsTail, liftExprArgs, enterFunction,
          bumpOutcome] <;>
        (repeat' split) <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget])
    | (cases ‹BodyOutcome› <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget, liftE, liftLE, liftAE,
          liftActiveCall, liftIndexLVal, liftArgsTail, liftExprArgs, enterFunction,
          bumpOutcome] <;>
        (repeat' split) <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget])
    | (cases ‹StmtOutcome› <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget, liftE, liftLE, liftAE,
          liftActiveCall, liftIndexLVal, liftArgsTail, liftExprArgs, enterFunction,
          bumpOutcome] <;>
        (repeat' split) <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget])
    | simp [ExprOutcomeNoValue, LValOutcomeNoTarget, bumpOutcome]

set_option linter.unusedSimpArgs false in
private theorem stepLValRel_noTarget (st : RuntimeState) :
    ∀ {lv o}, StepLVal st lv o → LValOutcomeNoTarget o := by
  apply @StepLVal.rec st
    (motive_1 := fun _ o _ => ExprOutcomeNoValue o)
    (motive_2 := fun _ o _ => LValOutcomeNoTarget o)
    (motive_3 := fun _ o _ => True)
    (motive_4 := fun _ o _ => True)
    (motive_5 := fun _ o _ => True)
  case callDef =>
    intros
    cases ‹ArgListOutcome›
    case values =>
      simp [liftAE, enterFunction]
      split <;> simp [ExprOutcomeNoValue]
    all_goals simp [liftAE, ExprOutcomeNoValue]
  case activeCall =>
    intros
    cases ‹BodyOutcome› <;> simp [liftActiveCall, ExprOutcomeNoValue]
    cases ‹Control› <;> simp [liftActiveCall, ExprOutcomeNoValue]
  all_goals intros
  all_goals
    first
    | trivial
    | (cases ‹ExprOutcome› <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget, liftE, liftLE, liftAE,
          liftActiveCall, liftIndexLVal, liftArgsTail, liftExprArgs, enterFunction,
          bumpOutcome] <;>
        (repeat' split) <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget])
    | (cases ‹LValOutcome› <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget, liftE, liftLE, liftAE,
          liftActiveCall, liftIndexLVal, liftArgsTail, liftExprArgs, enterFunction,
          bumpOutcome] <;>
        (repeat' split) <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget])
    | (cases ‹ArgListOutcome› <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget, liftE, liftLE, liftAE,
          liftActiveCall, liftIndexLVal, liftArgsTail, liftExprArgs, enterFunction,
          bumpOutcome] <;>
        (repeat' split) <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget])
    | (cases ‹BodyOutcome› <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget, liftE, liftLE, liftAE,
          liftActiveCall, liftIndexLVal, liftArgsTail, liftExprArgs, enterFunction,
          bumpOutcome] <;>
        (repeat' split) <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget])
    | (cases ‹StmtOutcome› <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget, liftE, liftLE, liftAE,
          liftActiveCall, liftIndexLVal, liftArgsTail, liftExprArgs, enterFunction,
          bumpOutcome] <;>
        (repeat' split) <;>
        simp [ExprOutcomeNoValue, LValOutcomeNoTarget])
    | simp [ExprOutcomeNoValue, LValOutcomeNoTarget, bumpOutcome]

/-- A `.value` step outcome only arises from the literal value term. -/
theorem stepExpr_value_inv {st e st' v} (h : stepExpr st e = .value st' v) :
    e = .value v ∧ st' = st := by
  by_cases hv : ExprTerm.isValue e = false
  · exfalso
    have hrel := stepExprRel_noValue st (stepExpr_complete (st := st) (e := e) hv)
    rw [h] at hrel
    simp [ExprOutcomeNoValue] at hrel
  · cases e <;> simp [ExprTerm.isValue] at hv
    simp [stepExpr] at h
    exact ⟨by rw [h.2], h.1.symm⟩

/-- A `.target` step outcome only arises from the literal target term. -/
theorem stepLVal_target_inv {st lv st' t} (h : stepLVal st lv = .target st' t) :
    lv = .target t ∧ st' = st := by
  by_cases hv : LValTerm.isTarget lv = false
  · exfalso
    have hrel := stepLValRel_noTarget st (stepLVal_complete (st := st) (lv := lv) hv)
    rw [h] at hrel
    simp [LValOutcomeNoTarget] at hrel
  · cases lv <;> simp [LValTerm.isTarget] at hv
    simp [stepLVal] at h
    exact ⟨by rw [h.2], h.1.symm⟩

/-- Argument-list steps preserve function lookups. -/
theorem stepArgs_next_lookupFunction {st args st' args'} (name : Name)
    (h : stepArgs st args = .next st' args') :
    lookupFunction st' name = lookupFunction st name := by
  have hl := stepArgs_lookupFunction (name := name) h
  simpa [ArgsOutcomeLookup] using hl

/-- Argument-list completion preserves function lookups. -/
theorem stepArgs_values_lookupFunction {st args st' values} (name : Name)
    (h : stepArgs st args = .values st' values) :
    lookupFunction st' name = lookupFunction st name := by
  have hl := stepArgs_lookupFunction (name := name) h
  simpa [ArgsOutcomeLookup] using hl

theorem stepExpr_call_args_next {name : Name} {defn : FunDef} {st args st' args'}
    (hlookup : lookupFunction st name = some defn)
    (h : stepArgs st args = .next st' args') :
    stepExpr st (.call name args) = .next st' (.call name args') := by
  simp [stepExpr, hlookup, h]

theorem stepExpr_call_args_control {name : Name} {defn : FunDef} {st args st' c}
    (hlookup : lookupFunction st name = some defn)
    (h : stepArgs st args = .control st' c) :
    stepExpr st (.call name args) = .control st' c := by
  simp [stepExpr, hlookup, h]

theorem stepExpr_call_args_error {name : Name} {defn : FunDef} {st args st' msg}
    (hlookup : lookupFunction st name = some defn)
    (h : stepArgs st args = .runtimeError st' msg) :
    stepExpr st (.call name args) = .runtimeError st' msg := by
  simp [stepExpr, hlookup, h]

private theorem ArgsRuns.lift_values_to_call {name : Name} {defn : FunDef}
    {st args stFinal values o}
    (hlookup : lookupFunction st name = some defn)
    (hvalues : ∀ {st₀ args₀}, lookupFunction st₀ name = some defn →
      stepArgs st₀ args₀ = .values stFinal values → ExprRuns st₀ (.call name args₀) o)
    (h : ArgsRuns st args (.values stFinal values)) :
    ExprRuns st (.call name args) o := by
  generalize hout : ArgListOutcome.values stFinal values = out at h
  induction h generalizing defn with
  | stop hstep _ =>
      cases hout
      exact hvalues hlookup hstep
  | next hstep _ ih =>
      have hlookup' := (stepArgs_lookupFunction name hstep)
      simp [ArgsOutcomeLookup, hlookup] at hlookup'
      exact ExprRuns.next (stepExpr_call_args_next hlookup hstep) (ih hlookup' hvalues hout)

private theorem ArgsRuns.lift_control_to_call {name : Name} {defn : FunDef}
    {st args stFinal c}
    (hlookup : lookupFunction st name = some defn)
    (h : ArgsRuns st args (.control stFinal c)) :
    ExprRuns st (.call name args) (.control stFinal c) := by
  generalize hout : ArgListOutcome.control stFinal c = out at h
  induction h generalizing defn with
  | stop hstep _ =>
      cases hout
      exact ExprRuns.control (stepExpr_call_args_control hlookup hstep)
  | next hstep _ ih =>
      have hlookup' := (stepArgs_lookupFunction name hstep)
      simp [ArgsOutcomeLookup, hlookup] at hlookup'
      exact ExprRuns.next (stepExpr_call_args_next hlookup hstep) (ih hlookup' hout)

private theorem ArgsRuns.lift_error_to_call {name : Name} {defn : FunDef}
    {st args stFinal msg}
    (hlookup : lookupFunction st name = some defn)
    (h : ArgsRuns st args (.runtimeError stFinal msg)) :
    ExprRuns st (.call name args) (.runtimeError stFinal msg) := by
  generalize hout : ArgListOutcome.runtimeError stFinal msg = out at h
  induction h generalizing defn with
  | stop hstep _ =>
      cases hout
      exact ExprRuns.runtimeError (stepExpr_call_args_error hlookup hstep)
  | next hstep _ ih =>
      have hlookup' := (stepArgs_lookupFunction name hstep)
      simp [ArgsOutcomeLookup, hlookup] at hlookup'
      exact ExprRuns.next (stepExpr_call_args_next hlookup hstep) (ih hlookup' hout)

/-!
The next two declarations were superseded by the lookup-preserving call lifts above.
-/
/-!
private theorem ArgsRuns.lift_control_to_call {name : Name} {defn : FunDef}
    {st args stFinal c}
    (hlookup : lookupFunction st name = some defn)
    (h : ArgsRuns st args (.control stFinal c)) :
    ExprRuns st (.call name args) (.control stFinal c) := by
  generalize hout : ArgListOutcome.control stFinal c = out at h
  induction h generalizing defn with
  | stop hstep _ =>
      cases hout
      exact ExprRuns.control (stepExpr_call_args_control hlookup hstep)
  | next (st' := stNext) hstep _ ih =>
      have hlookup' : lookupFunction stNext name = some defn := by
        have hp := stepArgs_lookupFunction name hstep
        simpa [ArgsOutcomeLookup, hlookup] using hp
      exact ExprRuns.next (stepExpr_call_args_next hlookup hstep) (ih hlookup' hout)

private theorem ArgsRuns.lift_error_to_call {name : Name} {defn : FunDef}
    {st args stFinal msg}
    (hlookup : lookupFunction st name = some defn)
    (h : ArgsRuns st args (.runtimeError stFinal msg)) :
    ExprRuns st (.call name args) (.runtimeError stFinal msg) := by
  generalize hout : ArgListOutcome.runtimeError stFinal msg = out at h
  induction h generalizing defn with
  | stop hstep _ =>
      cases hout
      exact ExprRuns.runtimeError (stepExpr_call_args_error hlookup hstep)
  | next (st' := stNext) hstep _ ih =>
      have hlookup' : lookupFunction stNext name = some defn := by
        have hp := stepArgs_lookupFunction name hstep
        simpa [ArgsOutcomeLookup, hlookup] using hp
      exact ExprRuns.next (stepExpr_call_args_next hlookup hstep) (ih hlookup' hout)
-/

private theorem forwardProps (fuel : Nat) : ForwardProps fuel := by
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
      cases fuel with
      | zero =>
          refine {
            expr := ?_, rel := ?_, lval := ?_, assign := ?_, unary := ?_, builtin := ?_,
            args := ?_, call := ?_, stmt := ?_, forLoop := ?_, stmts := ?_, body := ?_ }
          · intro st e r h hnf
            simp [evalExpr] at h
            subst r
            cases hnf
          · intro st left rest r h hnf
            simp [evalRelChain] at h
            subst r
            cases hnf
          · intro st lv r h hnf
            simp [evalLValueTarget] at h
            subst r
            cases hnf
          · intro st lhs op rhs r h hnf
            simp [evalAssign] at h
            subst r
            cases hnf
          · intro st op arg r h hnf
            simp [evalUnary] at h
            subst r
            cases hnf
          · intro st fn arg r h hnf
            simp [evalBuiltin] at h
            subst r
            cases hnf
          · intro st args r h hnf
            simp [evalArgValues] at h
            subst r
            cases hnf
          · intro st name args r h hnf
            simp [evalCall] at h
            subst r
            cases hnf
          · intro st stmt r h hnf
            simp [evalStmt] at h
            subst r
            cases hnf
          · intro st cond update body r h hnf
            simp [evalFor] at h
            subst r
            cases hnf
          · intro st stmts r h hnf
            simp [evalStmts] at h
            subst r
            cases hnf
          · intro st body r h hnf
            simp [evalBody] at h
            subst r
            cases hnf
      | succ fuel' =>
          have prev := ih fuel' (Nat.lt_succ_self fuel')
          refine {
            expr := ?_, rel := ?_, lval := ?_, assign := ?_, unary := ?_, builtin := ?_,
            args := ?_, call := ?_, stmt := ?_, forLoop := ?_, stmts := ?_, body := ?_ }
          · intro st e r h hnf
            cases e with
            | num raw =>
                cases h
                simpa [ExprTerm.ofExpr] using
                  (ExprRuns.next (by simp [stepExpr]) (ExprRuns.value : ExprRuns st (.value (Num.ofInputString raw (currentConstBase st))) (.value st (Num.ofInputString raw (currentConstBase st)))))
            | var name =>
                cases h
                simpa [ExprTerm.ofExpr] using
                  (ExprRuns.next (by simp [stepExpr]) (ExprRuns.value : ExprRuns st (.value (lookupScalar st name)) (.value st (lookupScalar st name))))
            | special v =>
                cases h
                simpa [ExprTerm.ofExpr] using
                  (ExprRuns.next (by simp [stepExpr]) (ExprRuns.value : ExprRuns st (.value (specialValue st v)) (.value st (specialValue st v))))
            | arrayAccess name idx =>
                simp only [evalExpr] at h
                simp only [ExprTerm.ofExpr]
                change ExprRuns st (.arrayAccess name (ExprTerm.ofExpr idx)) (evalToExprOutcome r)
                match hidx : evalExpr fuel' st idx with
                | .ok st' idxNum =>
                    match hindex : indexOfNum? idxNum with
                    | .ok idxNat =>
                        have hr : r = .ok (ensureArrayId st' name).1
                            (getArrayElem (ensureArrayId st' name).1 (ensureArrayId st' name).2 idxNat) := by
                          simpa [hidx, hindex] using h.symm
                        cases hr
                        have hidxRun := prev.expr st idx (.ok st' idxNum) hidx
                          (by simp [EvalResultNotFuel])
                        exact ExprRuns.lift_value (k := fun e => .arrayAccess name e)
                          (by intro st e st' e' hstep; exact stepExpr_arrayAccess_next hstep)
                          hidxRun
                          (ExprRuns.next (by simp [stepExpr, hindex]) ExprRuns.value)
                    | .error msg =>
                        have hr : r = .runtimeError st' msg := by
                          simpa [hidx, hindex] using h.symm
                        cases hr
                        have hidxRun := prev.expr st idx (.ok st' idxNum) hidx
                          (by simp [EvalResultNotFuel])
                        exact ExprRuns.lift_value (k := fun e => .arrayAccess name e)
                          (by intro st e st' e' hstep; exact stepExpr_arrayAccess_next hstep)
                          hidxRun
                          (ExprRuns.runtimeError (by simp [stepExpr, hindex]))
                | .control st' c =>
                    have hr : r = .control st' c := by simpa [hidx] using h.symm
                    cases hr
                    have hidxRun := prev.expr st idx (.control st' c) hidx (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_control (k := fun e => .arrayAccess name e)
                      (by intro st e st' e' hstep; exact stepExpr_arrayAccess_next hstep)
                      (by intro st e st' c hstep; exact stepExpr_arrayAccess_control hstep)
                      hidxRun
                | .outOfFuel st' =>
                    have hr : r = .outOfFuel st' := by simpa [hidx] using h.symm
                    cases hr
                    cases hnf
                | .runtimeError st' msg =>
                    have hr : r = .runtimeError st' msg := by simpa [hidx] using h.symm
                    cases hr
                    have hidxRun := prev.expr st idx (.runtimeError st' msg) hidx
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_error (k := fun e => .arrayAccess name e)
                      (by intro st e st' e' hstep; exact stepExpr_arrayAccess_next hstep)
                      (by intro st e st' msg hstep; exact stepExpr_arrayAccess_error hstep)
                      hidxRun
            | assign lhs op rhs =>
                simpa [ExprTerm.ofExpr] using
                  (prev.assign st lhs op rhs r (by simpa [evalExpr] using h) hnf)
            | rel first rest =>
                simp only [evalExpr] at h
                simp only [ExprTerm.ofExpr]
                change
                  ExprRuns st (.rel (ExprTerm.ofExpr first) (ExprTerm.ofRelRest rest))
                    (evalToExprOutcome r)
                match hfirst : evalExpr fuel' st first with
                | .ok st' n =>
                    have hrel := prev.rel st' n rest r (by simpa [hfirst] using h) hnf
                    have hfirstRun := prev.expr st first (.ok st' n) hfirst
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_value (k := fun e => .rel e (ExprTerm.ofRelRest rest))
                      (by intro st e st' e' hstep; exact stepExpr_rel_first_next hstep)
                      hfirstRun hrel
                | .control st' c =>
                    have hr : r = .control st' c := by simpa [hfirst] using h.symm
                    cases hr
                    have hfirstRun := prev.expr st first (.control st' c) hfirst
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_control (k := fun e => .rel e (ExprTerm.ofRelRest rest))
                      (by intro st e st' e' hstep; exact stepExpr_rel_first_next hstep)
                      (by intro st e st' c hstep; exact stepExpr_rel_first_control hstep)
                      hfirstRun
                | .outOfFuel st' =>
                    have hr : r = .outOfFuel st' := by simpa [hfirst] using h.symm
                    cases hr
                    cases hnf
                | .runtimeError st' msg =>
                    have hr : r = .runtimeError st' msg := by simpa [hfirst] using h.symm
                    cases hr
                    have hfirstRun := prev.expr st first (.runtimeError st' msg) hfirst
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_error (k := fun e => .rel e (ExprTerm.ofRelRest rest))
                      (by intro st e st' e' hstep; exact stepExpr_rel_first_next hstep)
                      (by intro st e st' msg hstep; exact stepExpr_rel_first_error hstep)
                      hfirstRun
            | bin op lhs rhs =>
                simp only [evalExpr] at h
                simp only [ExprTerm.ofExpr]
                change
                  ExprRuns st (.bin op (ExprTerm.ofExpr lhs) (ExprTerm.ofExpr rhs))
                    (evalToExprOutcome r)
                match hlhs : evalExpr fuel' st lhs with
                | .ok st₁ a =>
                    have hlhsRun := prev.expr st lhs (.ok st₁ a) hlhs (by simp [EvalResultNotFuel])
                    match hrhs : evalExpr fuel' st₁ rhs with
                    | .ok st₂ b =>
                        match hop : applyBin? op a b st₂.scale with
                        | .ok n =>
                            have hr : r = .ok st₂ n := by simpa [hlhs, hrhs, hop] using h.symm
                            cases hr
                            have hrhsRun := prev.expr st₁ rhs (.ok st₂ b) hrhs
                              (by simp [EvalResultNotFuel])
                            exact ExprRuns.lift_value (k := fun e => .bin op e (ExprTerm.ofExpr rhs))
                              (by intro st e st' e' hstep; exact stepExpr_bin_lhs_next hstep)
                              hlhsRun
                              (ExprRuns.lift_value
                                (k := fun e => .bin op (.value a) e)
                                (by intro st e st' e' hstep; exact stepExpr_bin_rhs_next hstep)
                                hrhsRun
                                (ExprRuns.bin_values_ok hop))
                        | .error msg =>
                            have hr : r = .runtimeError st₂ msg := by
                              simpa [hlhs, hrhs, hop] using h.symm
                            cases hr
                            have hrhsRun := prev.expr st₁ rhs (.ok st₂ b) hrhs
                              (by simp [EvalResultNotFuel])
                            exact ExprRuns.lift_value (k := fun e => .bin op e (ExprTerm.ofExpr rhs))
                              (by intro st e st' e' hstep; exact stepExpr_bin_lhs_next hstep)
                              hlhsRun
                              (ExprRuns.lift_value
                                (k := fun e => .bin op (.value a) e)
                                (by intro st e st' e' hstep; exact stepExpr_bin_rhs_next hstep)
                                hrhsRun
                                (ExprRuns.bin_values_error hop))
                    | .control st₂ c =>
                        have hr : r = .control st₂ c := by simpa [hlhs, hrhs] using h.symm
                        cases hr
                        have hrhsRun := prev.expr st₁ rhs (.control st₂ c) hrhs
                          (by simp [EvalResultNotFuel])
                        exact ExprRuns.lift_value (k := fun e => .bin op e (ExprTerm.ofExpr rhs))
                          (by intro st e st' e' hstep; exact stepExpr_bin_lhs_next hstep)
                          hlhsRun
                          (ExprRuns.lift_control
                            (k := fun e => .bin op (.value a) e)
                            (by intro st e st' e' hstep; exact stepExpr_bin_rhs_next hstep)
                            (by intro st e st' c hstep; exact stepExpr_bin_rhs_control hstep)
                            hrhsRun)
                    | .outOfFuel st₂ =>
                        have hr : r = .outOfFuel st₂ := by simpa [hlhs, hrhs] using h.symm
                        cases hr
                        cases hnf
                    | .runtimeError st₂ msg =>
                        have hr : r = .runtimeError st₂ msg := by simpa [hlhs, hrhs] using h.symm
                        cases hr
                        have hrhsRun := prev.expr st₁ rhs (.runtimeError st₂ msg) hrhs
                          (by simp [EvalResultNotFuel])
                        exact ExprRuns.lift_value (k := fun e => .bin op e (ExprTerm.ofExpr rhs))
                          (by intro st e st' e' hstep; exact stepExpr_bin_lhs_next hstep)
                          hlhsRun
                          (ExprRuns.lift_error
                            (k := fun e => .bin op (.value a) e)
                            (by intro st e st' e' hstep; exact stepExpr_bin_rhs_next hstep)
                            (by intro st e st' msg hstep; exact stepExpr_bin_rhs_error hstep)
                            hrhsRun)
                | .control st₁ c =>
                    have hr : r = .control st₁ c := by simpa [hlhs] using h.symm
                    cases hr
                    have hlhsRun := prev.expr st lhs (.control st₁ c) hlhs
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_control (k := fun e => .bin op e (ExprTerm.ofExpr rhs))
                      (by intro st e st' e' hstep; exact stepExpr_bin_lhs_next hstep)
                      (by intro st e st' c hstep; exact stepExpr_bin_lhs_control hstep)
                      hlhsRun
                | .outOfFuel st₁ =>
                    have hr : r = .outOfFuel st₁ := by simpa [hlhs] using h.symm
                    cases hr
                    cases hnf
                | .runtimeError st₁ msg =>
                    have hr : r = .runtimeError st₁ msg := by simpa [hlhs] using h.symm
                    cases hr
                    have hlhsRun := prev.expr st lhs (.runtimeError st₁ msg) hlhs
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_error (k := fun e => .bin op e (ExprTerm.ofExpr rhs))
                      (by intro st e st' e' hstep; exact stepExpr_bin_lhs_next hstep)
                      (by intro st e st' msg hstep; exact stepExpr_bin_lhs_error hstep)
                      hlhsRun
            | unary op arg =>
                exact prev.unary st op arg r (by simpa [evalExpr] using h) hnf
            | call name args =>
                simpa [ExprTerm.ofExpr] using
                  (prev.call st name args r (by simpa [evalExpr] using h) hnf)
            | builtin fn arg =>
                exact prev.builtin st fn arg r (by simpa [evalExpr] using h) hnf
            | paren body =>
                simp only [evalExpr] at h
                simp only [ExprTerm.ofExpr]
                change ExprRuns st (.paren (ExprTerm.ofExpr body)) (evalToExprOutcome r)
                match hbody : evalExpr fuel' st body with
                | .ok st' n =>
                    have hr : r = .ok st' n := by simpa [hbody] using h.symm
                    cases hr
                    have hbodyRun := prev.expr st body (.ok st' n) hbody
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_value (k := fun e => .paren e)
                      (by intro st e st' e' hstep; exact stepExpr_paren_next hstep)
                      hbodyRun
                      ExprRuns.paren_value
                | .control st' c =>
                    have hr : r = .control st' c := by simpa [hbody] using h.symm
                    cases hr
                    have hbodyRun := prev.expr st body (.control st' c) hbody
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_control (k := fun e => .paren e)
                      (by intro st e st' e' hstep; exact stepExpr_paren_next hstep)
                      (by intro st e st' c hstep; exact stepExpr_paren_control hstep)
                      hbodyRun
                | .outOfFuel st' =>
                    have hr : r = .outOfFuel st' := by simpa [hbody] using h.symm
                    cases hr
                    cases hnf
                | .runtimeError st' msg =>
                    have hr : r = .runtimeError st' msg := by simpa [hbody] using h.symm
                    cases hr
                    have hbodyRun := prev.expr st body (.runtimeError st' msg) hbody
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_error (k := fun e => .paren e)
                      (by intro st e st' e' hstep; exact stepExpr_paren_next hstep)
                      (by intro st e st' msg hstep; exact stepExpr_paren_error hstep)
                      hbodyRun
          · intro st left rest r h hnf
            simp only [evalRelChain] at h
            cases rest with
            | nil =>
                have hr : r = .ok st left := by simpa using h.symm
                cases hr
                simpa [ExprTerm.ofRelRest, evalToExprOutcome] using
                  (ExprRuns.rel_nil (st := st) (left := left))
            | cons head tail =>
                rcases head with ⟨op, rhs⟩
                match hrhs : evalExpr fuel' st rhs with
                | .ok st' right =>
                    let out := boolNum (applyRel op left right)
                    have hrhsRun := prev.expr st rhs (.ok st' right) hrhs
                      (by simp [EvalResultNotFuel])
                    cases tail with
                    | nil =>
                      have hr : r = .ok st' out := by
                        simpa [hrhs, out] using h.symm
                      cases hr
                      simpa [ExprTerm.ofRelRest, evalToExprOutcome, out] using
                        (ExprRuns.lift_value
                          (k := fun e => .rel (.value left) ((op, e) :: []))
                          (by intro st e st' e' hstep; exact stepExpr_rel_rhs_next hstep)
                          hrhsRun
                          (ExprRuns.rel_value_cons (tail := []) ExprRuns.value))
                    | cons pair tailRest =>
                      rcases pair with ⟨opTail, rhsTail⟩
                      have hrel := prev.rel st' out ((opTail, rhsTail) :: tailRest) r
                        (by simpa [hrhs, out] using h) hnf
                      simpa [ExprTerm.ofRelRest, evalToExprOutcome] using
                        (ExprRuns.lift_value
                          (k := fun e =>
                            .rel (.value left)
                              ((op, e) :: ExprTerm.ofRelRest ((opTail, rhsTail) :: tailRest)))
                          (by intro st e st' e' hstep; exact stepExpr_rel_rhs_next hstep)
                          hrhsRun
                          (ExprRuns.rel_value_cons
                            (tail := ExprTerm.ofRelRest ((opTail, rhsTail) :: tailRest))
                            (by simpa [ExprTerm.ofRelRest, out] using hrel)))
                | .control st' c =>
                    have hr : r = .control st' c := by simpa [hrhs] using h.symm
                    cases hr
                    have hrhsRun := prev.expr st rhs (.control st' c) hrhs
                      (by simp [EvalResultNotFuel])
                    simpa [ExprTerm.ofRelRest, evalToExprOutcome] using
                      (ExprRuns.lift_control
                        (k := fun e => .rel (.value left) ((op, e) :: ExprTerm.ofRelRest tail))
                        (by intro st e st' e' hstep; exact stepExpr_rel_rhs_next hstep)
                        (by intro st e st' c hstep; exact stepExpr_rel_rhs_control hstep)
                        hrhsRun)
                | .outOfFuel st' =>
                    have hr : r = .outOfFuel st' := by simpa [hrhs] using h.symm
                    cases hr
                    cases hnf
                | .runtimeError st' msg =>
                    have hr : r = .runtimeError st' msg := by simpa [hrhs] using h.symm
                    cases hr
                    have hrhsRun := prev.expr st rhs (.runtimeError st' msg) hrhs
                      (by simp [EvalResultNotFuel])
                    simpa [ExprTerm.ofRelRest, evalToExprOutcome] using
                      (ExprRuns.lift_error
                        (k := fun e => .rel (.value left) ((op, e) :: ExprTerm.ofRelRest tail))
                        (by intro st e st' e' hstep; exact stepExpr_rel_rhs_next hstep)
                        (by intro st e st' msg hstep; exact stepExpr_rel_rhs_error hstep)
                        hrhsRun)
          · intro st lv r h hnf
            cases lv with
            | var name =>
                have hr : r = .ok st (.scalar name) := by simpa [evalLValueTarget] using h.symm
                cases hr
                exact LValRuns.next (by simp [stepLVal, LValTerm.ofLVal]) LValRuns.target
            | special v =>
                have hr : r = .ok st (.special v) := by simpa [evalLValueTarget] using h.symm
                cases hr
                exact LValRuns.next (by simp [stepLVal, LValTerm.ofLVal]) LValRuns.target
            | array name idx =>
                simp only [evalLValueTarget] at h
                simp only [LValTerm.ofLVal]
                match hidx : evalExpr fuel' st idx with
                | .ok st' idxNum =>
                    match hindex : indexOfNum? idxNum with
                    | .ok idxNat =>
                        have hr : r = .ok (ensureArrayId st' name).1
                            (.arrayElem (ensureArrayId st' name).2 idxNat) := by
                          simpa [hidx, hindex] using h.symm
                        cases hr
                        have hidxRun := prev.expr st idx (.ok st' idxNum) hidx
                          (by simp [EvalResultNotFuel])
                        exact ExprRuns.lift_value_to_lval
                          (k := fun e => .array name e)
                          (by intro st e st' e' hstep; exact stepLVal_array_next hstep)
                          hidxRun
                          (LValRuns.array_value_ok (name := name) hindex)
                    | .error msg =>
                        have hr : r = .runtimeError st' msg := by
                          simpa [hidx, hindex] using h.symm
                        cases hr
                        have hidxRun := prev.expr st idx (.ok st' idxNum) hidx
                          (by simp [EvalResultNotFuel])
                        exact ExprRuns.lift_value_to_lval
                          (k := fun e => .array name e)
                          (by intro st e st' e' hstep; exact stepLVal_array_next hstep)
                          hidxRun
                          (LValRuns.array_value_error (name := name) hindex)
                | .control st' c =>
                    have hr : r = .runtimeError st'
                        "control escaped from lvalue evaluation" := by
                      simpa [hidx] using h.symm
                    cases hr
                    have hidxRun := prev.expr st idx (.control st' c) hidx
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_control_to_lval
                      (k := fun e => .array name e)
                      (by intro st e st' e' hstep; exact stepLVal_array_next hstep)
                      (by intro st e st' c hstep; exact stepLVal_array_control hstep)
                      hidxRun
                | .outOfFuel st' =>
                    have hr : r = .outOfFuel st' := by simpa [hidx] using h.symm
                    cases hr
                    cases hnf
                | .runtimeError st' msg =>
                    have hr : r = .runtimeError st' msg := by simpa [hidx] using h.symm
                    cases hr
                    have hidxRun := prev.expr st idx (.runtimeError st' msg) hidx
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_error_to_lval
                      (k := fun e => .array name e)
                      (by intro st e st' e' hstep; exact stepLVal_array_next hstep)
                      (by intro st e st' msg hstep; exact stepLVal_array_error hstep)
                      hidxRun
          · intro st lhs op rhs r h hnf
            simp only [evalAssign] at h
            match hlhs : evalLValueTarget fuel' st lhs with
            | .ok st₁ target =>
                have hlhsRun := prev.lval st lhs (.ok st₁ target) hlhs
                  (by simp [EvalResultNotFuel])
                match hrhs : evalExpr fuel' st₁ rhs with
                | .ok st₂ rhsValue =>
                    match happ : applyAssign? op (readLValueTarget st₂ target)
                        rhsValue st₂.scale with
                    | .ok result =>
                        have hr : r = .ok (writeLValueTarget st₂ target result) result := by
                          simpa [hlhs, hrhs, happ] using h.symm
                        cases hr
                        have hrhsRun := prev.expr st₁ rhs (.ok st₂ rhsValue) hrhs
                          (by simp [EvalResultNotFuel])
                        exact LValRuns.lift_target_to_expr
                          (k := fun lv => .assign lv op (ExprTerm.ofExpr rhs))
                          (by intro st lv st' lv' hstep; exact stepExpr_assign_lval_next hstep)
                          hlhsRun
                          (ExprRuns.next (by simp [stepExpr])
                              (ExprRuns.lift_value
                                (k := fun e => .assignTarget target op e)
                                (by
                                  intro st e st' e' hstep
                                  exact stepExpr_assignTarget_rhs_next hstep)
                              hrhsRun
                              (ExprRuns.assignTarget_value_ok happ)))
                    | .error msg =>
                        have hr : r = .runtimeError st₂ msg := by
                          simpa [hlhs, hrhs, happ] using h.symm
                        cases hr
                        have hrhsRun := prev.expr st₁ rhs (.ok st₂ rhsValue) hrhs
                          (by simp [EvalResultNotFuel])
                        exact LValRuns.lift_target_to_expr
                          (k := fun lv => .assign lv op (ExprTerm.ofExpr rhs))
                          (by intro st lv st' lv' hstep; exact stepExpr_assign_lval_next hstep)
                          hlhsRun
                          (ExprRuns.next (by simp [stepExpr])
                              (ExprRuns.lift_value
                                (k := fun e => .assignTarget target op e)
                                (by
                                  intro st e st' e' hstep
                                  exact stepExpr_assignTarget_rhs_next hstep)
                              hrhsRun
                              (ExprRuns.assignTarget_value_error happ)))
                | .control st₂ c =>
                    have hr : r = .control st₂ c := by simpa [hlhs, hrhs] using h.symm
                    cases hr
                    have hrhsRun := prev.expr st₁ rhs (.control st₂ c) hrhs
                      (by simp [EvalResultNotFuel])
                    exact LValRuns.lift_target_to_expr
                      (k := fun lv => .assign lv op (ExprTerm.ofExpr rhs))
                      (by intro st lv st' lv' hstep; exact stepExpr_assign_lval_next hstep)
                      hlhsRun
                      (ExprRuns.next (by simp [stepExpr])
                          (ExprRuns.lift_control
                            (k := fun e => .assignTarget target op e)
                            (by
                              intro st e st' e' hstep
                              exact stepExpr_assignTarget_rhs_next hstep)
                            (by
                              intro st e st' c hstep
                              exact stepExpr_assignTarget_rhs_control hstep)
                          hrhsRun))
                | .outOfFuel st₂ =>
                    have hr : r = .outOfFuel st₂ := by simpa [hlhs, hrhs] using h.symm
                    cases hr
                    cases hnf
                | .runtimeError st₂ msg =>
                    have hr : r = .runtimeError st₂ msg := by simpa [hlhs, hrhs] using h.symm
                    cases hr
                    have hrhsRun := prev.expr st₁ rhs (.runtimeError st₂ msg) hrhs
                      (by simp [EvalResultNotFuel])
                    exact LValRuns.lift_target_to_expr
                      (k := fun lv => .assign lv op (ExprTerm.ofExpr rhs))
                      (by intro st lv st' lv' hstep; exact stepExpr_assign_lval_next hstep)
                      hlhsRun
                      (ExprRuns.next (by simp [stepExpr])
                          (ExprRuns.lift_error
                            (k := fun e => .assignTarget target op e)
                            (by
                              intro st e st' e' hstep
                              exact stepExpr_assignTarget_rhs_next hstep)
                            (by
                              intro st e st' msg hstep
                              exact stepExpr_assignTarget_rhs_error hstep)
                          hrhsRun))
            | .control st₁ c =>
                exact False.elim (evalLValueTarget_ne_control (fuel := fuel') (st := st)
                  (lv := lhs) (st' := st₁) (c := c) hlhs)
            | .outOfFuel st₁ =>
                have hr : r = .outOfFuel st₁ := by simpa [hlhs] using h.symm
                cases hr
                cases hnf
            | .runtimeError st₁ msg =>
                have hr : r = .runtimeError st₁ msg := by simpa [hlhs] using h.symm
                cases hr
                have hlhsRun := prev.lval st lhs (.runtimeError st₁ msg) hlhs
                  (by simp [EvalResultNotFuel])
                exact LValRuns.lift_error_to_expr
                  (k := fun lv => .assign lv op (ExprTerm.ofExpr rhs))
                  (by intro st lv st' lv' hstep; exact stepExpr_assign_lval_next hstep)
                  (by intro st lv st' msg hstep; exact stepExpr_assign_lval_error hstep)
                  hlhsRun
          · intro st op arg r h hnf
            cases op with
            | neg =>
                simp only [evalUnary] at h
                simp only [ExprTerm.ofExpr]
                match harg : evalExpr fuel' st arg with
                | .ok st' value =>
                    have hr : r = .ok st' (Num.neg value) := by simpa [harg] using h.symm
                    cases hr
                    have hargRun := prev.expr st arg (.ok st' value) harg
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_value
                      (k := fun e => .neg e)
                      (by intro st e st' e' hstep; exact stepExpr_neg_next hstep)
                      hargRun
                      ExprRuns.neg_value
                | .control st' c =>
                    have hr : r = .control st' c := by simpa [harg] using h.symm
                    cases hr
                    have hargRun := prev.expr st arg (.control st' c) harg
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_control
                      (k := fun e => .neg e)
                      (by intro st e st' e' hstep; exact stepExpr_neg_next hstep)
                      (by intro st e st' c hstep; exact stepExpr_neg_control hstep)
                      hargRun
                | .outOfFuel st' =>
                    have hr : r = .outOfFuel st' := by simpa [harg] using h.symm
                    cases hr
                    cases hnf
                | .runtimeError st' msg =>
                    have hr : r = .runtimeError st' msg := by simpa [harg] using h.symm
                    cases hr
                    have hargRun := prev.expr st arg (.runtimeError st' msg) harg
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_error
                      (k := fun e => .neg e)
                      (by intro st e st' e' hstep; exact stepExpr_neg_next hstep)
                      (by intro st e st' msg hstep; exact stepExpr_neg_error hstep)
                      hargRun
            | preIncr =>
                exact unaryBump_from_eval (op := .preIncr) prev
                  (by rfl)
                  (by intro hlv; simp [ExprTerm.ofExpr, LValTerm.ofExpr?_eq, hlv])
                  (by intro lv hlv; simp [ExprTerm.ofExpr, LValTerm.ofExpr?_eq, hlv])
                  h hnf
            | preDecr =>
                exact unaryBump_from_eval (op := .preDecr) prev
                  (by rfl)
                  (by intro hlv; simp [ExprTerm.ofExpr, LValTerm.ofExpr?_eq, hlv])
                  (by intro lv hlv; simp [ExprTerm.ofExpr, LValTerm.ofExpr?_eq, hlv])
                  h hnf
            | postIncr =>
                exact unaryBump_from_eval (op := .postIncr) prev
                  (by rfl)
                  (by intro hlv; simp [ExprTerm.ofExpr, LValTerm.ofExpr?_eq, hlv])
                  (by intro lv hlv; simp [ExprTerm.ofExpr, LValTerm.ofExpr?_eq, hlv])
                  h hnf
            | postDecr =>
                exact unaryBump_from_eval (op := .postDecr) prev
                  (by rfl)
                  (by intro hlv; simp [ExprTerm.ofExpr, LValTerm.ofExpr?_eq, hlv])
                  (by intro lv hlv; simp [ExprTerm.ofExpr, LValTerm.ofExpr?_eq, hlv])
                  h hnf
          · intro st fn arg r h hnf
            cases arg with
            | none =>
                have hr : r = .runtimeError st "invalid builtin arity" := by
                  simpa [evalBuiltin] using h.symm
                cases hr
                simpa [ExprTerm.ofExpr, evalToExprOutcome] using
                  (ExprRuns.builtin_none (st := st) (fn := fn))
            | some e =>
                simp only [evalBuiltin] at h
                simp only [ExprTerm.ofExpr]
                match he : evalExpr fuel' st e with
                | .ok st' n =>
                    have heRun := prev.expr st e (.ok st' n) he (by simp [EvalResultNotFuel])
                    match hb : applyBuiltin? fn n st'.scale with
                    | .ok out =>
                        have hr : r = .ok st' out := by simpa [he, hb] using h.symm
                        cases hr
                        exact ExprRuns.lift_value
                          (k := fun e => .builtin fn (some e))
                          (by intro st e st' e' hstep; exact stepExpr_builtin_arg_next hstep)
                          heRun
                          (ExprRuns.builtin_value_ok hb)
                    | .error msg =>
                        have hr : r = .runtimeError st' msg := by simpa [he, hb] using h.symm
                        cases hr
                        exact ExprRuns.lift_value
                          (k := fun e => .builtin fn (some e))
                          (by intro st e st' e' hstep; exact stepExpr_builtin_arg_next hstep)
                          heRun
                          (ExprRuns.builtin_value_error hb)
                | .control st' c =>
                    have hr : r = .control st' c := by simpa [he] using h.symm
                    cases hr
                    have heRun := prev.expr st e (.control st' c) he (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_control
                      (k := fun e => .builtin fn (some e))
                      (by intro st e st' e' hstep; exact stepExpr_builtin_arg_next hstep)
                      (by intro st e st' c hstep; exact stepExpr_builtin_arg_control hstep)
                      heRun
                | .outOfFuel st' =>
                    have hr : r = .outOfFuel st' := by simpa [he] using h.symm
                    cases hr
                    cases hnf
                | .runtimeError st' msg =>
                    have hr : r = .runtimeError st' msg := by simpa [he] using h.symm
                    cases hr
                    have heRun := prev.expr st e (.runtimeError st' msg) he
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_error
                      (k := fun e => .builtin fn (some e))
                      (by intro st e st' e' hstep; exact stepExpr_builtin_arg_next hstep)
                      (by intro st e st' msg hstep; exact stepExpr_builtin_arg_error hstep)
                      heRun
          · intro st args r h hnf
            cases args with
            | nil =>
                have hr : r = .ok st [] := by simpa [evalArgValues] using h.symm
                cases hr
                exact ArgsRuns.stop (by simp [stepArgs, ArgTerm.ofArgs, evalToArgsOutcome])
                  (by simp [ArgsFinal, evalToArgsOutcome])
            | cons arg rest =>
                cases arg with
                | expr e =>
                    simp only [evalArgValues] at h
                    simp only [ArgTerm.ofArgs, ArgTerm.ofArg]
                    match he : evalExpr fuel' st e with
                    | .ok st₁ v =>
                        have heRun := prev.expr st e (.ok st₁ v) he
                          (by simp [EvalResultNotFuel])
                        match hrest : evalArgValues fuel' st₁ rest with
                        | .ok st₂ values =>
                            have hr : r = .ok st₂ (.inl v :: values) := by
                              simpa [he, hrest] using h.symm
                            cases hr
                            have hrestRun := prev.args st₁ rest (.ok st₂ values) hrest
                              (by simp [EvalResultNotFuel])
                            exact ExprRuns.lift_value_to_args
                              (k := fun e => .expr e :: ArgTerm.ofArgs rest)
                              (by intro st e st' e' hstep; exact stepArgs_expr_head_next hstep)
                              heRun
                              (ArgsRuns.lift_tail_values
                                (k := fun restTerms => .expr (.value v) :: restTerms)
                                (kv := fun values => Sum.inl v :: values)
                                (by
                                  intro st args st' args' hstep
                                  exact stepArgs_expr_value_tail_next hstep)
                                (by
                                  intro st args st' values hstep
                                  exact stepArgs_expr_value_tail_values hstep)
                                hrestRun)
                        | .control st₂ c =>
                            have hr : r = .control st₂ c := by simpa [he, hrest] using h.symm
                            cases hr
                            have hrestRun := prev.args st₁ rest (.control st₂ c) hrest
                              (by simp [EvalResultNotFuel])
                            exact ExprRuns.lift_value_to_args
                              (k := fun e => .expr e :: ArgTerm.ofArgs rest)
                              (by intro st e st' e' hstep; exact stepArgs_expr_head_next hstep)
                              heRun
                              (ArgsRuns.lift_tail_control
                                (k := fun restTerms => .expr (.value v) :: restTerms)
                                (by
                                  intro st args st' args' hstep
                                  exact stepArgs_expr_value_tail_next hstep)
                                (by
                                  intro st args st' c hstep
                                  exact stepArgs_expr_value_tail_control hstep)
                                hrestRun)
                        | .outOfFuel st₂ =>
                            have hr : r = .outOfFuel st₂ := by simpa [he, hrest] using h.symm
                            cases hr
                            cases hnf
                        | .runtimeError st₂ msg =>
                            have hr : r = .runtimeError st₂ msg := by
                              simpa [he, hrest] using h.symm
                            cases hr
                            have hrestRun := prev.args st₁ rest (.runtimeError st₂ msg) hrest
                              (by simp [EvalResultNotFuel])
                            exact ExprRuns.lift_value_to_args
                              (k := fun e => .expr e :: ArgTerm.ofArgs rest)
                              (by intro st e st' e' hstep; exact stepArgs_expr_head_next hstep)
                              heRun
                              (ArgsRuns.lift_tail_error
                                (k := fun restTerms => .expr (.value v) :: restTerms)
                                (by
                                  intro st args st' args' hstep
                                  exact stepArgs_expr_value_tail_next hstep)
                                (by
                                  intro st args st' msg hstep
                                  exact stepArgs_expr_value_tail_error hstep)
                                hrestRun)
                    | .control st₁ c =>
                        have hr : r = .control st₁ c := by simpa [he] using h.symm
                        cases hr
                        have heRun := prev.expr st e (.control st₁ c) he
                          (by simp [EvalResultNotFuel])
                        exact ExprRuns.lift_control_to_args
                          (k := fun e => .expr e :: ArgTerm.ofArgs rest)
                          (by intro st e st' e' hstep; exact stepArgs_expr_head_next hstep)
                          (by intro st e st' c hstep; exact stepArgs_expr_head_control hstep)
                          heRun
                    | .outOfFuel st₁ =>
                        have hr : r = .outOfFuel st₁ := by simpa [he] using h.symm
                        cases hr
                        cases hnf
                    | .runtimeError st₁ msg =>
                        have hr : r = .runtimeError st₁ msg := by simpa [he] using h.symm
                        cases hr
                        have heRun := prev.expr st e (.runtimeError st₁ msg) he
                          (by simp [EvalResultNotFuel])
                        exact ExprRuns.lift_error_to_args
                          (k := fun e => .expr e :: ArgTerm.ofArgs rest)
                          (by intro st e st' e' hstep; exact stepArgs_expr_head_next hstep)
                          (by intro st e st' msg hstep; exact stepArgs_expr_head_error hstep)
                          heRun
                | arrayRef name =>
                    simp only [evalArgValues] at h
                    simp only [ArgTerm.ofArgs, ArgTerm.ofArg]
                    match hrest : evalArgValues fuel' st rest with
                    | .ok st₁ values =>
                        have hr : r = .ok st₁ (.inr name :: values) := by
                          simpa [hrest] using h.symm
                        cases hr
                        have hrestRun := prev.args st rest (.ok st₁ values) hrest
                          (by simp [EvalResultNotFuel])
                        exact ArgsRuns.lift_tail_values
                          (k := fun restTerms => .arrayRef name :: restTerms)
                          (kv := fun values => Sum.inr name :: values)
                          (by
                            intro st args st' args' hstep
                            exact stepArgs_arrayRef_tail_next hstep)
                          (by
                            intro st args st' values hstep
                            exact stepArgs_arrayRef_tail_values hstep)
                          hrestRun
                    | .control st₁ c =>
                        have hr : r = .control st₁ c := by simpa [hrest] using h.symm
                        cases hr
                        have hrestRun := prev.args st rest (.control st₁ c) hrest
                          (by simp [EvalResultNotFuel])
                        exact ArgsRuns.lift_tail_control
                          (k := fun restTerms => .arrayRef name :: restTerms)
                          (by
                            intro st args st' args' hstep
                            exact stepArgs_arrayRef_tail_next hstep)
                          (by
                            intro st args st' c hstep
                            exact stepArgs_arrayRef_tail_control hstep)
                          hrestRun
                    | .outOfFuel st₁ =>
                        have hr : r = .outOfFuel st₁ := by simpa [hrest] using h.symm
                        cases hr
                        cases hnf
                    | .runtimeError st₁ msg =>
                        have hr : r = .runtimeError st₁ msg := by simpa [hrest] using h.symm
                        cases hr
                        have hrestRun := prev.args st rest (.runtimeError st₁ msg) hrest
                          (by simp [EvalResultNotFuel])
                        exact ArgsRuns.lift_tail_error
                          (k := fun restTerms => .arrayRef name :: restTerms)
                          (by
                            intro st args st' args' hstep
                            exact stepArgs_arrayRef_tail_next hstep)
                          (by
                            intro st args st' msg hstep
                            exact stepArgs_arrayRef_tail_error hstep)
                          hrestRun
          · intro st name args r h hnf
            simp only [evalCall] at h
            simp only [evalToExprOutcome]
            match hlookup : lookupFunction st name with
            | none =>
                have hr : r = .runtimeError st s!"Function {name} not defined" := by
                  simpa [hlookup] using h.symm
                cases hr
                exact ExprRuns.runtimeError (by simp [stepExpr, hlookup])
            | some defn =>
                match hargs : evalArgValues fuel' st args with
                | .ok st₁ argValues =>
                    have hargsRun := prev.args st args (.ok st₁ argValues) hargs
                      (by simp [EvalResultNotFuel])
                    let frame : Frame := { constBase := st₁.ibase }
                    let stWithFrame : RuntimeState := { st₁ with frames := frame :: st₁.frames }
                    match hbind : bindParams stWithFrame defn.params argValues with
                    | .error msg =>
                        have hr : r = .runtimeError stWithFrame msg := by
                          simpa [hlookup, hargs, frame, stWithFrame, hbind] using h.symm
                        cases hr
                        exact ArgsRuns.lift_values_to_call hlookup
                          (by
                            intro st₀ args₀ hlookup₀ hstep
                            exact ExprRuns.runtimeError
                              (by
                                simp [stepExpr, hlookup₀, hstep, enterFunction, frame,
                                  stWithFrame, hbind]))
                          hargsRun
                    | .ok st₂ =>
                        let stBody := bindAutoDecls st₂ (collectAutos defn.body)
                        match hbody : evalBody fuel' stBody defn.body with
                        | .ok st₃ .normal =>
                            have hr : r = .ok (popFrame st₃) Num.zero := by
                              simpa [hlookup, hargs, frame, stWithFrame, hbind, stBody,
                                hbody, popFrame] using h.symm
                            cases hr
                            have hbodyRun := prev.body stBody defn.body (.ok st₃ .normal)
                              hbody (by simp [ResultNotFuel])
                            exact ArgsRuns.lift_values_to_call hlookup
                              (by
                                intro st₀ args₀ hlookup₀ hstep
                                exact ExprRuns.next
                                  (by
                                    simp [stepExpr, hlookup₀, hstep, enterFunction, frame,
                                      stWithFrame, hbind, stBody])
                                  (BodyRuns.lift_done_to_activeCall hbodyRun))
                              hargsRun
                        | .ok st₃ (.return value?) =>
                            have hr : r = .ok (popFrame st₃) (returnValue value?) := by
                              cases value? <;>
                                simpa [hlookup, hargs, frame, stWithFrame, hbind, stBody,
                                  hbody, popFrame, returnValue] using h.symm
                            cases hr
                            have hbodyRun := prev.body stBody defn.body (.ok st₃ (.return value?))
                              hbody (by simp [ResultNotFuel])
                            exact ArgsRuns.lift_values_to_call hlookup
                              (by
                                intro st₀ args₀ hlookup₀ hstep
                                have hactive :
                                    ExprRuns stBody (.activeCall (BodyTerm.ofBody defn.body))
                                      (.value (popFrame st₃) (returnValue value?)) := by
                                  simpa [evalToExprOutcome, returnValue] using
                                    (BodyRuns.lift_control_to_activeCall hbodyRun)
                                exact ExprRuns.next
                                  (by
                                    simp [stepExpr, hlookup₀, hstep, enterFunction, frame,
                                      stWithFrame, hbind, stBody])
                                  hactive)
                              hargsRun
                        | .ok st₃ .break =>
                            have hr : r =
                                .runtimeError (popFrame st₃) "Break outside a loop" := by
                              simpa [hlookup, hargs, frame, stWithFrame, hbind, stBody,
                                hbody, popFrame] using h.symm
                            cases hr
                            have hbodyRun := prev.body stBody defn.body (.ok st₃ .break)
                              hbody (by simp [ResultNotFuel])
                            exact ArgsRuns.lift_values_to_call hlookup
                              (by
                                intro st₀ args₀ hlookup₀ hstep
                                have hactive :
                                    ExprRuns stBody (.activeCall (BodyTerm.ofBody defn.body))
                                      (.runtimeError (popFrame st₃) "Break outside a loop") := by
                                  simpa [evalToExprOutcome] using
                                    (BodyRuns.lift_control_to_activeCall hbodyRun)
                                exact ExprRuns.next
                                  (by
                                    simp [stepExpr, hlookup₀, hstep, enterFunction, frame,
                                      stWithFrame, hbind, stBody])
                                  hactive)
                              hargsRun
                        | .ok st₃ .quit =>
                            have hr : r = .control (popFrame st₃) .quit := by
                              simpa [hlookup, hargs, frame, stWithFrame, hbind, stBody,
                                hbody, popFrame] using h.symm
                            cases hr
                            have hbodyRun := prev.body stBody defn.body (.ok st₃ .quit)
                              hbody (by simp [ResultNotFuel])
                            exact ArgsRuns.lift_values_to_call hlookup
                              (by
                                intro st₀ args₀ hlookup₀ hstep
                                have hactive :
                                    ExprRuns stBody (.activeCall (BodyTerm.ofBody defn.body))
                                      (.control (popFrame st₃) .quit) := by
                                  simpa [evalToExprOutcome] using
                                    (BodyRuns.lift_control_to_activeCall hbodyRun)
                                exact ExprRuns.next
                                  (by
                                    simp [stepExpr, hlookup₀, hstep, enterFunction, frame,
                                      stWithFrame, hbind, stBody])
                                  hactive)
                              hargsRun
                        | .outOfFuel st₃ =>
                            have hr : r = .outOfFuel (popFrame st₃) := by
                              simpa [hlookup, hargs, frame, stWithFrame, hbind, stBody,
                                hbody, popFrame] using h.symm
                            cases hr
                            cases hnf
                        | .runtimeError st₃ msg =>
                            have hr : r = .runtimeError (popFrame st₃) msg := by
                              simpa [hlookup, hargs, frame, stWithFrame, hbind, stBody,
                                hbody, popFrame] using h.symm
                            cases hr
                            have hbodyRun := prev.body stBody defn.body (.runtimeError st₃ msg)
                              hbody (by simp [ResultNotFuel])
                            exact ArgsRuns.lift_values_to_call hlookup
                              (by
                                intro st₀ args₀ hlookup₀ hstep
                                exact ExprRuns.next
                                  (by
                                    simp [stepExpr, hlookup₀, hstep, enterFunction, frame,
                                      stWithFrame, hbind, stBody])
                                  (BodyRuns.lift_error_to_activeCall hbodyRun))
                              hargsRun
                | .control st₁ c =>
                    have hr : r = .control st₁ c := by
                      simpa [hlookup, hargs] using h.symm
                    cases hr
                    have hargsRun := prev.args st args (.control st₁ c) hargs
                      (by simp [EvalResultNotFuel])
                    exact ArgsRuns.lift_control_to_call hlookup hargsRun
                | .outOfFuel st₁ =>
                    have hr : r = .outOfFuel st₁ := by
                      simpa [hlookup, hargs] using h.symm
                    cases hr
                    cases hnf
                | .runtimeError st₁ msg =>
                    have hr : r = .runtimeError st₁ msg := by
                      simpa [hlookup, hargs] using h.symm
                    cases hr
                    have hargsRun := prev.args st args (.runtimeError st₁ msg) hargs
                      (by simp [EvalResultNotFuel])
                    exact ArgsRuns.lift_error_to_call hlookup hargsRun
          · intro st stmt r h hnf
            match stmt with
            | .expr e =>
                simp only [evalStmt] at h
                simp only [StmtTerm.ofStmt, evalToStmtOutcome]
                match he : evalExpr fuel' st e with
                | .ok st₁ value =>
                    have heRun := prev.expr st e (.ok st₁ value) he
                      (by simp [EvalResultNotFuel])
                    by_cases htop : isTopAssignment e
                    · have hr : r = .ok st₁ .normal := by
                        simpa [he, htop] using h.symm
                      cases hr
                      exact ExprRuns.lift_value_to_stmt
                        (k := fun term => .expr e term)
                        (by intro st e st' e' hstep; exact stepStmt_expr_next hstep)
                        heRun
                        (StmtRuns.stop
                          (by simp [stepStmt, htop])
                          (by simp [StmtFinal]))
                    · have hr : r = .ok (printNumLine st₁ value) .normal := by
                        simpa [he, htop] using h.symm
                      cases hr
                      exact ExprRuns.lift_value_to_stmt
                        (k := fun term => .expr e term)
                        (by intro st e st' e' hstep; exact stepStmt_expr_next hstep)
                        heRun
                        (StmtRuns.stop
                          (by simp [stepStmt, htop])
                          (by simp [StmtFinal]))
                | .control st₁ c =>
                    have hr : r = .ok st₁ c := by
                      simpa [he] using h.symm
                    cases hr
                    have heRun := prev.expr st e (.control st₁ c) he
                      (by simp [EvalResultNotFuel])
                    cases c
                    · exact False.elim (ExprRuns.no_control_normal heRun)
                    · simpa using
                        (ExprRuns.lift_control_to_stmt
                          (k := fun term => .expr e term)
                          (by intro st e st' e' hstep; exact stepStmt_expr_next hstep)
                          (by intro st e st' c hstep; exact stepStmt_expr_control hstep)
                          heRun)
                    · simpa using
                        (ExprRuns.lift_control_to_stmt
                          (k := fun term => .expr e term)
                          (by intro st e st' e' hstep; exact stepStmt_expr_next hstep)
                          (by intro st e st' c hstep; exact stepStmt_expr_control hstep)
                          heRun)
                    · simpa using
                        (ExprRuns.lift_control_to_stmt
                          (k := fun term => .expr e term)
                          (by intro st e st' e' hstep; exact stepStmt_expr_next hstep)
                          (by intro st e st' c hstep; exact stepStmt_expr_control hstep)
                          heRun)
                | .outOfFuel st₁ =>
                    have hr : r = .outOfFuel st₁ := by
                      simpa [he] using h.symm
                    cases hr
                    cases hnf
                | .runtimeError st₁ msg =>
                    have hr : r = .runtimeError st₁ msg := by
                      simpa [he] using h.symm
                    cases hr
                    have heRun := prev.expr st e (.runtimeError st₁ msg) he
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_error_to_stmt
                      (k := fun term => .expr e term)
                      (by intro st e st' e' hstep; exact stepStmt_expr_next hstep)
                      (by intro st e st' msg hstep; exact stepStmt_expr_error hstep)
                      heRun
            | .str s =>
                have hr : r = .ok (appendOutput st (decodeBcString s)) .normal := by
                  simpa [evalStmt] using h.symm
                cases hr
                simpa [evalToStmtOutcome] using
                  (StmtRuns.stop
                    (by simp [StmtTerm.ofStmt, stepStmt])
                    (by simp [StmtFinal]))
            | .auto params =>
                have hr : r = .ok st .normal := by
                  simpa [evalStmt] using h.symm
                cases hr
                simpa [evalToStmtOutcome] using
                  (StmtRuns.stop
                    (by simp [StmtTerm.ofStmt, stepStmt])
                    (by simp [StmtFinal]))
            | .if cond thenBranch =>
                simp only [evalStmt] at h
                simp only [StmtTerm.ofStmt, evalToStmtOutcome]
                match hcond : evalExpr fuel' st cond with
                | .ok st₁ condValue =>
                    have hcondRun := prev.expr st cond (.ok st₁ condValue) hcond
                      (by simp [EvalResultNotFuel])
                    by_cases hzero : condValue.isZero
                    · have hr : r = .ok st₁ .normal := by
                        simpa [hcond, hzero] using h.symm
                      cases hr
                      exact ExprRuns.lift_value_to_stmt
                        (k := fun e => .ifThen e (StmtTerm.ofStmt thenBranch))
                        (by intro st e st' e' hstep; exact stepStmt_if_next hstep)
                        hcondRun
                        (StmtRuns.stop
                          (by simp [stepStmt, hzero])
                          (by simp [StmtFinal]))
                    · have hthenEval : evalStmt fuel' st₁ thenBranch = r := by
                        simpa [hcond, hzero] using h
                      have hthenRun := prev.stmt st₁ thenBranch r hthenEval hnf
                      exact ExprRuns.lift_value_to_stmt
                        (k := fun e => .ifThen e (StmtTerm.ofStmt thenBranch))
                        (by intro st e st' e' hstep; exact stepStmt_if_next hstep)
                        hcondRun
                        (StmtRuns.next (by simp [stepStmt, hzero]) hthenRun)
                | .control st₁ c =>
                    have hr : r = .ok st₁ c := by
                      simpa [hcond] using h.symm
                    cases hr
                    have hcondRun := prev.expr st cond (.control st₁ c) hcond
                      (by simp [EvalResultNotFuel])
                    cases c
                    · exact False.elim (ExprRuns.no_control_normal hcondRun)
                    · simpa using
                        (ExprRuns.lift_control_to_stmt
                          (k := fun e => .ifThen e (StmtTerm.ofStmt thenBranch))
                          (by intro st e st' e' hstep; exact stepStmt_if_next hstep)
                          (by intro st e st' c hstep; exact stepStmt_if_control hstep)
                          hcondRun)
                    · simpa using
                        (ExprRuns.lift_control_to_stmt
                          (k := fun e => .ifThen e (StmtTerm.ofStmt thenBranch))
                          (by intro st e st' e' hstep; exact stepStmt_if_next hstep)
                          (by intro st e st' c hstep; exact stepStmt_if_control hstep)
                          hcondRun)
                    · simpa using
                        (ExprRuns.lift_control_to_stmt
                          (k := fun e => .ifThen e (StmtTerm.ofStmt thenBranch))
                          (by intro st e st' e' hstep; exact stepStmt_if_next hstep)
                          (by intro st e st' c hstep; exact stepStmt_if_control hstep)
                          hcondRun)
                | .outOfFuel st₁ =>
                    have hr : r = .outOfFuel st₁ := by
                      simpa [hcond] using h.symm
                    cases hr
                    cases hnf
                | .runtimeError st₁ msg =>
                    have hr : r = .runtimeError st₁ msg := by
                      simpa [hcond] using h.symm
                    cases hr
                    have hcondRun := prev.expr st cond (.runtimeError st₁ msg) hcond
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_error_to_stmt
                      (k := fun e => .ifThen e (StmtTerm.ofStmt thenBranch))
                      (by intro st e st' e' hstep; exact stepStmt_if_next hstep)
                      (by intro st e st' msg hstep; exact stepStmt_if_error hstep)
                      hcondRun
            | .while cond body =>
                simp only [evalStmt] at h
                simp only [StmtTerm.ofStmt, evalToStmtOutcome]
                let bodyTerm := StmtTerm.ofStmt body
                let afterTerm := StmtTerm.while cond (ExprTerm.ofExpr cond) bodyTerm
                match hcond : evalExpr fuel' st cond with
                | .ok st₁ condValue =>
                    have hcondRun := prev.expr st cond (.ok st₁ condValue) hcond
                      (by simp [EvalResultNotFuel])
                    by_cases hzero : condValue.isZero
                    · have hr : r = .ok st₁ .normal := by
                        simpa [hcond, hzero] using h.symm
                      cases hr
                      exact ExprRuns.lift_value_to_stmt
                        (k := fun e => .while cond e bodyTerm)
                        (by intro st e st' e' hstep; exact stepStmt_while_next hstep)
                        hcondRun
                        (StmtRuns.stop
                          (by simp [stepStmt, hzero])
                          (by simp [StmtFinal]))
                    · match hbody : evalStmt fuel' st₁ body with
                      | .ok st₂ .normal =>
                          have hrecEval : evalStmt fuel' st₂ (.while cond body) = r := by
                            simpa [hcond, hzero, hbody] using h
                          have hbodyRun := prev.stmt st₁ body (.ok st₂ .normal) hbody
                            (by simp [ResultNotFuel])
                          have hrecRun := prev.stmt st₂ (.while cond body) r hrecEval hnf
                          have hloop :
                              StmtRuns st₁ (.loopBody bodyTerm afterTerm)
                                (evalToStmtOutcome r) :=
                            StmtRuns.lift_done_to_loop (after := afterTerm) hbodyRun
                              (by simpa [afterTerm, bodyTerm, StmtTerm.ofStmt] using hrecRun)
                          exact ExprRuns.lift_value_to_stmt
                            (k := fun e => .while cond e bodyTerm)
                            (by intro st e st' e' hstep; exact stepStmt_while_next hstep)
                            hcondRun
                            (StmtRuns.next
                              (by simp [stepStmt, hzero, bodyTerm, afterTerm])
                              hloop)
                      | .ok st₂ .break =>
                          have hr : r = .ok st₂ .normal := by
                            simpa [hcond, hzero, hbody] using h.symm
                          cases hr
                          have hbodyRun := prev.stmt st₁ body (.ok st₂ .break) hbody
                            (by simp [ResultNotFuel])
                          have hloop :
                              StmtRuns st₁ (.loopBody bodyTerm afterTerm) (.done st₂) :=
                            StmtRuns.lift_break_to_loop (after := afterTerm) hbodyRun
                          exact ExprRuns.lift_value_to_stmt
                            (k := fun e => .while cond e bodyTerm)
                            (by intro st e st' e' hstep; exact stepStmt_while_next hstep)
                            hcondRun
                            (StmtRuns.next
                              (by simp [stepStmt, hzero, bodyTerm, afterTerm])
                              hloop)
                      | .ok st₂ (.return value?) =>
                          have hr : r = .ok st₂ (.return value?) := by
                            simpa [hcond, hzero, hbody] using h.symm
                          cases hr
                          have hbodyRun := prev.stmt st₁ body (.ok st₂ (.return value?))
                            hbody (by simp [ResultNotFuel])
                          have hloop :
                              StmtRuns st₁ (.loopBody bodyTerm afterTerm)
                                (.control st₂ (.return value?)) :=
                            StmtRuns.lift_control_to_loop
                              (after := afterTerm) (by simp) hbodyRun
                          exact ExprRuns.lift_value_to_stmt
                            (k := fun e => .while cond e bodyTerm)
                            (by intro st e st' e' hstep; exact stepStmt_while_next hstep)
                            hcondRun
                            (StmtRuns.next
                              (by simp [stepStmt, hzero, bodyTerm, afterTerm])
                              hloop)
                      | .ok st₂ .quit =>
                          have hr : r = .ok st₂ .quit := by
                            simpa [hcond, hzero, hbody] using h.symm
                          cases hr
                          have hbodyRun := prev.stmt st₁ body (.ok st₂ .quit)
                            hbody (by simp [ResultNotFuel])
                          have hloop :
                              StmtRuns st₁ (.loopBody bodyTerm afterTerm)
                                (.control st₂ .quit) :=
                            StmtRuns.lift_control_to_loop
                              (after := afterTerm) (by simp) hbodyRun
                          exact ExprRuns.lift_value_to_stmt
                            (k := fun e => .while cond e bodyTerm)
                            (by intro st e st' e' hstep; exact stepStmt_while_next hstep)
                            hcondRun
                            (StmtRuns.next
                              (by simp [stepStmt, hzero, bodyTerm, afterTerm])
                              hloop)
                      | .outOfFuel st₂ =>
                          have hr : r = .outOfFuel st₂ := by
                            simpa [hcond, hzero, hbody] using h.symm
                          cases hr
                          cases hnf
                      | .runtimeError st₂ msg =>
                          have hr : r = .runtimeError st₂ msg := by
                            simpa [hcond, hzero, hbody] using h.symm
                          cases hr
                          have hbodyRun := prev.stmt st₁ body (.runtimeError st₂ msg) hbody
                            (by simp [ResultNotFuel])
                          have hloop :
                              StmtRuns st₁ (.loopBody bodyTerm afterTerm)
                                (.runtimeError st₂ msg) :=
                            StmtRuns.lift_error_to_loop (after := afterTerm) hbodyRun
                          exact ExprRuns.lift_value_to_stmt
                            (k := fun e => .while cond e bodyTerm)
                            (by intro st e st' e' hstep; exact stepStmt_while_next hstep)
                            hcondRun
                            (StmtRuns.next
                              (by simp [stepStmt, hzero, bodyTerm, afterTerm])
                              hloop)
                | .control st₁ c =>
                    have hr : r = .ok st₁ c := by
                      simpa [hcond] using h.symm
                    cases hr
                    have hcondRun := prev.expr st cond (.control st₁ c) hcond
                      (by simp [EvalResultNotFuel])
                    cases c
                    · exact False.elim (ExprRuns.no_control_normal hcondRun)
                    · simpa [bodyTerm] using
                        (ExprRuns.lift_control_to_stmt
                          (k := fun e => .while cond e bodyTerm)
                          (by intro st e st' e' hstep; exact stepStmt_while_next hstep)
                          (by intro st e st' c hstep; exact stepStmt_while_control hstep)
                          hcondRun)
                    · simpa [bodyTerm] using
                        (ExprRuns.lift_control_to_stmt
                          (k := fun e => .while cond e bodyTerm)
                          (by intro st e st' e' hstep; exact stepStmt_while_next hstep)
                          (by intro st e st' c hstep; exact stepStmt_while_control hstep)
                          hcondRun)
                    · simpa [bodyTerm] using
                        (ExprRuns.lift_control_to_stmt
                          (k := fun e => .while cond e bodyTerm)
                          (by intro st e st' e' hstep; exact stepStmt_while_next hstep)
                          (by intro st e st' c hstep; exact stepStmt_while_control hstep)
                          hcondRun)
                | .outOfFuel st₁ =>
                    have hr : r = .outOfFuel st₁ := by
                      simpa [hcond] using h.symm
                    cases hr
                    cases hnf
                | .runtimeError st₁ msg =>
                    have hr : r = .runtimeError st₁ msg := by
                      simpa [hcond] using h.symm
                    cases hr
                    have hcondRun := prev.expr st cond (.runtimeError st₁ msg) hcond
                      (by simp [EvalResultNotFuel])
                    exact ExprRuns.lift_error_to_stmt
                      (k := fun e => .while cond e bodyTerm)
                      (by intro st e st' e' hstep; exact stepStmt_while_next hstep)
                      (by intro st e st' msg hstep; exact stepStmt_while_error hstep)
                      hcondRun
            | .for init cond update body =>
                simp only [evalStmt] at h
                simp only [StmtTerm.ofStmt, evalToStmtOutcome]
                let bodyTerm := StmtTerm.ofStmt body
                let forTerm := StmtTerm.forCheck cond (ExprTerm.ofExpr cond) update bodyTerm
                match hinit : evalExpr fuel' st init with
                | .ok st₁ initValue =>
                    have hinitRun := prev.expr st init (.ok st₁ initValue) hinit
                      (by simp [EvalResultNotFuel])
                    have hforEval : evalFor fuel' st₁ cond update body = r := by
                      simpa [hinit] using h
                    have hforRun := prev.forLoop st₁ cond update body r hforEval hnf
                    have hevalRun :
                        StmtRuns st (.eval (ExprTerm.ofExpr init)) (.done st₁) := by
                      exact ExprRuns.lift_value_to_stmt
                        (k := fun e => .eval e)
                        (by intro st e st' e' hstep; exact stepStmt_eval_next hstep)
                        hinitRun
                        (StmtRuns.stop
                          (by simp [stepStmt])
                          (by simp [StmtFinal]))
                    exact StmtRuns.lift_done_to_seq
                      (second := forTerm) hevalRun (by simpa [forTerm] using hforRun)
                | .control st₁ c =>
                    have hr : r = .ok st₁ c := by
                      simpa [hinit] using h.symm
                    cases hr
                    have hinitRun := prev.expr st init (.control st₁ c) hinit
                      (by simp [EvalResultNotFuel])
                    have hevalRun :
                        StmtRuns st (.eval (ExprTerm.ofExpr init)) (.control st₁ c) := by
                      exact ExprRuns.lift_control_to_stmt
                        (k := fun e => .eval e)
                        (by intro st e st' e' hstep; exact stepStmt_eval_next hstep)
                        (by intro st e st' c hstep; exact stepStmt_eval_control hstep)
                        hinitRun
                    cases c
                    · exact False.elim (ExprRuns.no_control_normal hinitRun)
                    · exact StmtRuns.lift_control_to_seq (second := forTerm) hevalRun
                    · exact StmtRuns.lift_control_to_seq (second := forTerm) hevalRun
                    · exact StmtRuns.lift_control_to_seq (second := forTerm) hevalRun
                | .outOfFuel st₁ =>
                    have hr : r = .outOfFuel st₁ := by
                      simpa [hinit] using h.symm
                    cases hr
                    cases hnf
                | .runtimeError st₁ msg =>
                    have hr : r = .runtimeError st₁ msg := by
                      simpa [hinit] using h.symm
                    cases hr
                    have hinitRun := prev.expr st init (.runtimeError st₁ msg) hinit
                      (by simp [EvalResultNotFuel])
                    have hevalRun :
                        StmtRuns st (.eval (ExprTerm.ofExpr init))
                          (.runtimeError st₁ msg) := by
                      exact ExprRuns.lift_error_to_stmt
                        (k := fun e => .eval e)
                        (by intro st e st' e' hstep; exact stepStmt_eval_next hstep)
                        (by intro st e st' msg hstep; exact stepStmt_eval_error hstep)
                        hinitRun
                    exact StmtRuns.lift_error_to_seq (second := forTerm) hevalRun
            | .break =>
                have hr : r = .ok st .break := by
                  simpa [evalStmt] using h.symm
                cases hr
                simpa [evalToStmtOutcome] using
                  (StmtRuns.stop
                    (by simp [StmtTerm.ofStmt, stepStmt])
                    (by simp [StmtFinal]))
            | .return value? =>
                cases value? with
                | none =>
                    have hr : r = .ok st (.return none) := by
                      simpa [evalStmt] using h.symm
                    cases hr
                    simpa [evalToStmtOutcome] using
                      (StmtRuns.stop
                        (by simp [StmtTerm.ofStmt, stepStmt])
                        (by simp [StmtFinal]))
                | some e =>
                    simp only [evalStmt] at h
                    simp only [StmtTerm.ofStmt, evalToStmtOutcome]
                    match he : evalExpr fuel' st e with
                    | .ok st₁ value =>
                        have hr : r = .ok st₁ (.return (some value)) := by
                          simpa [he] using h.symm
                        cases hr
                        have heRun := prev.expr st e (.ok st₁ value) he
                          (by simp [EvalResultNotFuel])
                        exact ExprRuns.lift_value_to_stmt
                          (k := fun e => .return (some e))
                          (by intro st e st' e' hstep; exact stepStmt_return_next hstep)
                          heRun
                          (StmtRuns.stop
                            (by simp [stepStmt])
                            (by simp [StmtFinal]))
                    | .control st₁ c =>
                        have hr : r = .ok st₁ c := by
                          simpa [he] using h.symm
                        cases hr
                        have heRun := prev.expr st e (.control st₁ c) he
                          (by simp [EvalResultNotFuel])
                        cases c
                        · exact False.elim (ExprRuns.no_control_normal heRun)
                        · simpa using
                            (ExprRuns.lift_control_to_stmt
                              (k := fun e => .return (some e))
                              (by intro st e st' e' hstep; exact stepStmt_return_next hstep)
                              (by intro st e st' c hstep; exact stepStmt_return_control hstep)
                              heRun)
                        · simpa using
                            (ExprRuns.lift_control_to_stmt
                              (k := fun e => .return (some e))
                              (by intro st e st' e' hstep; exact stepStmt_return_next hstep)
                              (by intro st e st' c hstep; exact stepStmt_return_control hstep)
                              heRun)
                        · simpa using
                            (ExprRuns.lift_control_to_stmt
                              (k := fun e => .return (some e))
                              (by intro st e st' e' hstep; exact stepStmt_return_next hstep)
                              (by intro st e st' c hstep; exact stepStmt_return_control hstep)
                              heRun)
                    | .outOfFuel st₁ =>
                        have hr : r = .outOfFuel st₁ := by
                          simpa [he] using h.symm
                        cases hr
                        cases hnf
                    | .runtimeError st₁ msg =>
                        have hr : r = .runtimeError st₁ msg := by
                          simpa [he] using h.symm
                        cases hr
                        have heRun := prev.expr st e (.runtimeError st₁ msg) he
                          (by simp [EvalResultNotFuel])
                        exact ExprRuns.lift_error_to_stmt
                          (k := fun e => .return (some e))
                          (by intro st e st' e' hstep; exact stepStmt_return_next hstep)
                          (by intro st e st' msg hstep; exact stepStmt_return_error hstep)
                          heRun
            | .quit =>
                have hr : r = .ok { st with stopped := true } .quit := by
                  simpa [evalStmt] using h.symm
                cases hr
                simpa [evalToStmtOutcome] using
                  (StmtRuns.stop
                    (by simp [StmtTerm.ofStmt, stepStmt])
                    (by simp [StmtFinal]))
            | .block body =>
                simp only [evalStmt] at h
                simp only [StmtTerm.ofStmt, evalToStmtOutcome]
                match hbody : evalBody fuel' st body with
                | .ok st₁ .normal =>
                    have hr : r = .ok st₁ .normal := by
                      simpa [hbody] using h.symm
                    cases hr
                    have hbodyRun := prev.body st body (.ok st₁ .normal) hbody
                      (by simp [ResultNotFuel])
                    simpa [BodyTerm.ofBody] using
                      (BodyRuns.lift_done_to_block hbodyRun)
                | .ok st₁ .break =>
                    have hr : r = .ok st₁ .break := by
                      simpa [hbody] using h.symm
                    cases hr
                    have hbodyRun := prev.body st body (.ok st₁ .break) hbody
                      (by simp [ResultNotFuel])
                    simpa [BodyTerm.ofBody] using
                      (BodyRuns.lift_control_to_block hbodyRun)
                | .ok st₁ (.return value?) =>
                    have hr : r = .ok st₁ (.return value?) := by
                      simpa [hbody] using h.symm
                    cases hr
                    have hbodyRun := prev.body st body (.ok st₁ (.return value?)) hbody
                      (by simp [ResultNotFuel])
                    simpa [BodyTerm.ofBody] using
                      (BodyRuns.lift_control_to_block hbodyRun)
                | .ok st₁ .quit =>
                    have hr : r = .ok st₁ .quit := by
                      simpa [hbody] using h.symm
                    cases hr
                    have hbodyRun := prev.body st body (.ok st₁ .quit) hbody
                      (by simp [ResultNotFuel])
                    simpa [BodyTerm.ofBody] using
                      (BodyRuns.lift_control_to_block hbodyRun)
                | .outOfFuel st₁ =>
                    have hr : r = .outOfFuel st₁ := by
                      simpa [hbody] using h.symm
                    cases hr
                    cases hnf
                | .runtimeError st₁ msg =>
                    have hr : r = .runtimeError st₁ msg := by
                      simpa [hbody] using h.symm
                    cases hr
                    have hbodyRun := prev.body st body (.runtimeError st₁ msg) hbody
                      (by simp [ResultNotFuel])
                    simpa [BodyTerm.ofBody] using
                      (BodyRuns.lift_error_to_block hbodyRun)
          · intro st cond update body r h hnf
            simp only [evalFor] at h
            simp only [evalToStmtOutcome]
            let bodyTerm := StmtTerm.ofStmt body
            let updateTerm := ExprTerm.ofExpr update
            let afterTerm := StmtTerm.forUpdate cond update updateTerm bodyTerm
            match hcond : evalExpr fuel' st cond with
            | .ok st₁ condValue =>
                have hcondRun := prev.expr st cond (.ok st₁ condValue) hcond
                  (by simp [EvalResultNotFuel])
                by_cases hzero : condValue.isZero
                · have hr : r = .ok st₁ .normal := by
                    simpa [hcond, hzero] using h.symm
                  cases hr
                  exact ExprRuns.lift_value_to_stmt
                    (k := fun e => .forCheck cond e update bodyTerm)
                    (by intro st e st' e' hstep; exact stepStmt_forCheck_next hstep)
                    hcondRun
                    (StmtRuns.stop
                      (by simp [stepStmt, hzero])
                      (by simp [StmtFinal]))
                · match hbody : evalStmt fuel' st₁ body with
                  | .ok st₂ .normal =>
                      have hbodyRun := prev.stmt st₁ body (.ok st₂ .normal) hbody
                        (by simp [ResultNotFuel])
                      match hupdate : evalExpr fuel' st₂ update with
                      | .ok st₃ updateValue =>
                          have hrecEval : evalFor fuel' st₃ cond update body = r := by
                            simpa [hcond, hzero, hbody, hupdate] using h
                          have hrecRun := prev.forLoop st₃ cond update body r hrecEval hnf
                          have hupdateRun := prev.expr st₂ update (.ok st₃ updateValue)
                            hupdate (by simp [EvalResultNotFuel])
                          have hafter :
                              StmtRuns st₂ afterTerm (evalToStmtOutcome r) := by
                            exact ExprRuns.lift_value_to_stmt
                              (k := fun e => .forUpdate cond update e bodyTerm)
                              (by
                                intro st e st' e' hstep
                                exact stepStmt_forUpdate_next hstep)
                              hupdateRun
                              (StmtRuns.next (by simp [stepStmt, bodyTerm])
                                hrecRun)
                          have hloop :
                              StmtRuns st₁ (.loopBody bodyTerm afterTerm)
                                (evalToStmtOutcome r) :=
                            StmtRuns.lift_done_to_loop (after := afterTerm) hbodyRun hafter
                          exact ExprRuns.lift_value_to_stmt
                            (k := fun e => .forCheck cond e update bodyTerm)
                            (by
                              intro st e st' e' hstep
                              exact stepStmt_forCheck_next hstep)
                            hcondRun
                            (StmtRuns.next
                              (by simp [stepStmt, hzero, afterTerm, bodyTerm, updateTerm])
                              hloop)
                      | .control st₃ c =>
                          have hr : r = .ok st₃ c := by
                            simpa [hcond, hzero, hbody, hupdate] using h.symm
                          cases hr
                          have hupdateRun := prev.expr st₂ update (.control st₃ c)
                            hupdate (by simp [EvalResultNotFuel])
                          have hafter : StmtRuns st₂ afterTerm (.control st₃ c) := by
                            exact ExprRuns.lift_control_to_stmt
                              (k := fun e => .forUpdate cond update e bodyTerm)
                              (by
                                intro st e st' e' hstep
                                exact stepStmt_forUpdate_next hstep)
                              (by
                                intro st e st' c hstep
                                exact stepStmt_forUpdate_control hstep)
                              hupdateRun
                          have hloop : StmtRuns st₁ (.loopBody bodyTerm afterTerm)
                              (.control st₃ c) :=
                            StmtRuns.lift_done_to_loop (after := afterTerm) hbodyRun hafter
                          cases c
                          · exact False.elim (ExprRuns.no_control_normal hupdateRun)
                          · exact ExprRuns.lift_value_to_stmt
                              (k := fun e => .forCheck cond e update bodyTerm)
                              (by
                                intro st e st' e' hstep
                                exact stepStmt_forCheck_next hstep)
                              hcondRun
                              (StmtRuns.next
                                (by simp [stepStmt, hzero, afterTerm, bodyTerm, updateTerm])
                                hloop)
                          · exact ExprRuns.lift_value_to_stmt
                              (k := fun e => .forCheck cond e update bodyTerm)
                              (by
                                intro st e st' e' hstep
                                exact stepStmt_forCheck_next hstep)
                              hcondRun
                              (StmtRuns.next
                                (by simp [stepStmt, hzero, afterTerm, bodyTerm, updateTerm])
                                hloop)
                          · exact ExprRuns.lift_value_to_stmt
                              (k := fun e => .forCheck cond e update bodyTerm)
                              (by
                                intro st e st' e' hstep
                                exact stepStmt_forCheck_next hstep)
                              hcondRun
                              (StmtRuns.next
                                (by simp [stepStmt, hzero, afterTerm, bodyTerm, updateTerm])
                                hloop)
                      | .outOfFuel st₃ =>
                          have hr : r = .outOfFuel st₃ := by
                            simpa [hcond, hzero, hbody, hupdate] using h.symm
                          cases hr
                          cases hnf
                      | .runtimeError st₃ msg =>
                          have hr : r = .runtimeError st₃ msg := by
                            simpa [hcond, hzero, hbody, hupdate] using h.symm
                          cases hr
                          have hupdateRun := prev.expr st₂ update (.runtimeError st₃ msg)
                            hupdate (by simp [EvalResultNotFuel])
                          have hafter : StmtRuns st₂ afterTerm (.runtimeError st₃ msg) := by
                            exact ExprRuns.lift_error_to_stmt
                              (k := fun e => .forUpdate cond update e bodyTerm)
                              (by
                                intro st e st' e' hstep
                                exact stepStmt_forUpdate_next hstep)
                              (by
                                intro st e st' msg hstep
                                exact stepStmt_forUpdate_error hstep)
                              hupdateRun
                          have hloop : StmtRuns st₁ (.loopBody bodyTerm afterTerm)
                              (.runtimeError st₃ msg) :=
                            StmtRuns.lift_done_to_loop (after := afterTerm) hbodyRun hafter
                          exact ExprRuns.lift_value_to_stmt
                            (k := fun e => .forCheck cond e update bodyTerm)
                            (by
                              intro st e st' e' hstep
                              exact stepStmt_forCheck_next hstep)
                            hcondRun
                            (StmtRuns.next
                              (by simp [stepStmt, hzero, afterTerm, bodyTerm, updateTerm])
                              hloop)
                  | .ok st₂ .break =>
                      have hr : r = .ok st₂ .normal := by
                        simpa [hcond, hzero, hbody] using h.symm
                      cases hr
                      have hbodyRun := prev.stmt st₁ body (.ok st₂ .break) hbody
                        (by simp [ResultNotFuel])
                      have hloop : StmtRuns st₁ (.loopBody bodyTerm afterTerm) (.done st₂) :=
                        StmtRuns.lift_break_to_loop (after := afterTerm) hbodyRun
                      exact ExprRuns.lift_value_to_stmt
                        (k := fun e => .forCheck cond e update bodyTerm)
                        (by intro st e st' e' hstep; exact stepStmt_forCheck_next hstep)
                        hcondRun
                        (StmtRuns.next
                          (by simp [stepStmt, hzero, afterTerm, bodyTerm, updateTerm]) hloop)
                  | .ok st₂ (.return value?) =>
                      have hr : r = .ok st₂ (.return value?) := by
                        simpa [hcond, hzero, hbody] using h.symm
                      cases hr
                      have hbodyRun := prev.stmt st₁ body (.ok st₂ (.return value?)) hbody
                        (by simp [ResultNotFuel])
                      have hloop :
                          StmtRuns st₁ (.loopBody bodyTerm afterTerm)
                            (.control st₂ (.return value?)) :=
                        StmtRuns.lift_control_to_loop
                          (after := afterTerm) (by simp) hbodyRun
                      exact ExprRuns.lift_value_to_stmt
                        (k := fun e => .forCheck cond e update bodyTerm)
                        (by intro st e st' e' hstep; exact stepStmt_forCheck_next hstep)
                        hcondRun
                        (StmtRuns.next
                          (by simp [stepStmt, hzero, afterTerm, bodyTerm, updateTerm]) hloop)
                  | .ok st₂ .quit =>
                      have hr : r = .ok st₂ .quit := by
                        simpa [hcond, hzero, hbody] using h.symm
                      cases hr
                      have hbodyRun := prev.stmt st₁ body (.ok st₂ .quit) hbody
                        (by simp [ResultNotFuel])
                      have hloop :
                          StmtRuns st₁ (.loopBody bodyTerm afterTerm) (.control st₂ .quit) :=
                        StmtRuns.lift_control_to_loop
                          (after := afterTerm) (by simp) hbodyRun
                      exact ExprRuns.lift_value_to_stmt
                        (k := fun e => .forCheck cond e update bodyTerm)
                        (by intro st e st' e' hstep; exact stepStmt_forCheck_next hstep)
                        hcondRun
                        (StmtRuns.next
                          (by simp [stepStmt, hzero, afterTerm, bodyTerm, updateTerm]) hloop)
                  | .outOfFuel st₂ =>
                      have hr : r = .outOfFuel st₂ := by
                        simpa [hcond, hzero, hbody] using h.symm
                      cases hr
                      cases hnf
                  | .runtimeError st₂ msg =>
                      have hr : r = .runtimeError st₂ msg := by
                        simpa [hcond, hzero, hbody] using h.symm
                      cases hr
                      have hbodyRun := prev.stmt st₁ body (.runtimeError st₂ msg) hbody
                        (by simp [ResultNotFuel])
                      have hloop :
                          StmtRuns st₁ (.loopBody bodyTerm afterTerm)
                            (.runtimeError st₂ msg) :=
                        StmtRuns.lift_error_to_loop (after := afterTerm) hbodyRun
                      exact ExprRuns.lift_value_to_stmt
                        (k := fun e => .forCheck cond e update bodyTerm)
                        (by intro st e st' e' hstep; exact stepStmt_forCheck_next hstep)
                        hcondRun
                        (StmtRuns.next
                          (by simp [stepStmt, hzero, afterTerm, bodyTerm, updateTerm]) hloop)
            | .control st₁ c =>
                have hr : r = .ok st₁ c := by
                  simpa [hcond] using h.symm
                cases hr
                have hcondRun := prev.expr st cond (.control st₁ c) hcond
                  (by simp [EvalResultNotFuel])
                cases c
                · exact False.elim (ExprRuns.no_control_normal hcondRun)
                · simpa [bodyTerm] using
                    (ExprRuns.lift_control_to_stmt
                      (k := fun e => .forCheck cond e update bodyTerm)
                      (by intro st e st' e' hstep; exact stepStmt_forCheck_next hstep)
                      (by intro st e st' c hstep; exact stepStmt_forCheck_control hstep)
                      hcondRun)
                · simpa [bodyTerm] using
                    (ExprRuns.lift_control_to_stmt
                      (k := fun e => .forCheck cond e update bodyTerm)
                      (by intro st e st' e' hstep; exact stepStmt_forCheck_next hstep)
                      (by intro st e st' c hstep; exact stepStmt_forCheck_control hstep)
                      hcondRun)
                · simpa [bodyTerm] using
                    (ExprRuns.lift_control_to_stmt
                      (k := fun e => .forCheck cond e update bodyTerm)
                      (by intro st e st' e' hstep; exact stepStmt_forCheck_next hstep)
                      (by intro st e st' c hstep; exact stepStmt_forCheck_control hstep)
                      hcondRun)
            | .outOfFuel st₁ =>
                have hr : r = .outOfFuel st₁ := by
                  simpa [hcond] using h.symm
                cases hr
                cases hnf
            | .runtimeError st₁ msg =>
                have hr : r = .runtimeError st₁ msg := by
                  simpa [hcond] using h.symm
                cases hr
                have hcondRun := prev.expr st cond (.runtimeError st₁ msg) hcond
                  (by simp [EvalResultNotFuel])
                exact ExprRuns.lift_error_to_stmt
                  (k := fun e => .forCheck cond e update bodyTerm)
                  (by intro st e st' e' hstep; exact stepStmt_forCheck_next hstep)
                  (by intro st e st' msg hstep; exact stepStmt_forCheck_error hstep)
                  hcondRun
          · intro st stmts r h hnf
            cases stmts with
            | nil =>
                have hr : r = .ok st .normal := by
                  simpa [evalStmts] using h.symm
                cases hr
                exact BodyRuns.stop
                  (by simp [stepBody, StmtTerm.ofStmts, evalToBodyOutcome])
                  (by simp [BodyFinal, evalToBodyOutcome])
            | cons stmt rest =>
                simp only [evalStmts] at h
                simp only [StmtTerm.ofStmts]
                match hstmt : evalStmt fuel' st stmt with
                | .ok st₁ .normal =>
                    have hstmtRun := prev.stmt st stmt (.ok st₁ .normal) hstmt
                      (by simp [ResultNotFuel])
                    have hrestRun := prev.stmts st₁ rest r (by simpa [hstmt] using h) hnf
                    exact StmtRuns.lift_done_to_body hstmtRun hrestRun
                | .ok st₁ .break =>
                    have hr : r = .ok st₁ .break := by
                      simpa [hstmt] using h.symm
                    cases hr
                    have hstmtRun := prev.stmt st stmt (.ok st₁ .break) hstmt
                      (by simp [ResultNotFuel])
                    simpa [evalToBodyOutcome] using
                      (StmtRuns.lift_control_to_body
                        (rest := StmtTerm.ofStmts rest) hstmtRun)
                | .ok st₁ (.return value?) =>
                    have hr : r = .ok st₁ (.return value?) := by
                      simpa [hstmt] using h.symm
                    cases hr
                    have hstmtRun := prev.stmt st stmt (.ok st₁ (.return value?)) hstmt
                      (by simp [ResultNotFuel])
                    simpa [evalToBodyOutcome] using
                      (StmtRuns.lift_control_to_body
                        (rest := StmtTerm.ofStmts rest) hstmtRun)
                | .ok st₁ .quit =>
                    have hr : r = .ok st₁ .quit := by
                      simpa [hstmt] using h.symm
                    cases hr
                    have hstmtRun := prev.stmt st stmt (.ok st₁ .quit) hstmt
                      (by simp [ResultNotFuel])
                    simpa [evalToBodyOutcome] using
                      (StmtRuns.lift_control_to_body
                        (rest := StmtTerm.ofStmts rest) hstmtRun)
                | .outOfFuel st₁ =>
                    have hr : r = .outOfFuel st₁ := by
                      simpa [hstmt] using h.symm
                    cases hr
                    cases hnf
                | .runtimeError st₁ msg =>
                    have hr : r = .runtimeError st₁ msg := by
                      simpa [hstmt] using h.symm
                    cases hr
                    have hstmtRun := prev.stmt st stmt (.runtimeError st₁ msg) hstmt
                      (by simp [ResultNotFuel])
                    simpa [evalToBodyOutcome] using
                      (StmtRuns.lift_error_to_body
                        (rest := StmtTerm.ofStmts rest) hstmtRun)
          · intro st body r h hnf
            cases body with
            | nil =>
                have hr : r = .ok st .normal := by
                  simpa [evalBody] using h.symm
                cases hr
                exact BodyRuns.stop
                  (by simp [stepBody, BodyTerm.ofBody, BodyTerm.ofBodyItems,
                    evalToBodyOutcome])
                  (by simp [BodyFinal, evalToBodyOutcome])
            | cons item rest =>
                cases item with
                | newline =>
                    have hrest : evalBody fuel' st rest = r := by
                      simpa [evalBody] using h
                    have hrestRun := prev.body st rest r hrest hnf
                    simpa [BodyTerm.ofBody, BodyTerm.ofBodyItems] using hrestRun
                | stmts ss =>
                    simp only [evalBody] at h
                    simp only [BodyTerm.ofBody, BodyTerm.ofBodyItems]
                    match hss : evalStmts fuel' st ss with
                    | .ok st₁ .normal =>
                        have hssRun := prev.stmts st ss (.ok st₁ .normal) hss
                          (by simp [ResultNotFuel])
                        have hrestEval : evalBody fuel' st₁ rest = r := by
                          simpa [hss] using h
                        have hrestRun := prev.body st₁ rest r hrestEval hnf
                        exact BodyRuns.lift_done_to_append hssRun
                          (by simpa [BodyTerm.ofBody] using hrestRun)
                    | .ok st₁ .break =>
                        have hr : r = .ok st₁ .break := by
                          simpa [hss] using h.symm
                        cases hr
                        have hssRun := prev.stmts st ss (.ok st₁ .break) hss
                          (by simp [ResultNotFuel])
                        simpa [evalToBodyOutcome] using
                          (BodyRuns.lift_control_to_append
                            (rest := BodyTerm.ofBodyItems rest) hssRun)
                    | .ok st₁ (.return value?) =>
                        have hr : r = .ok st₁ (.return value?) := by
                          simpa [hss] using h.symm
                        cases hr
                        have hssRun := prev.stmts st ss (.ok st₁ (.return value?)) hss
                          (by simp [ResultNotFuel])
                        simpa [evalToBodyOutcome] using
                          (BodyRuns.lift_control_to_append
                            (rest := BodyTerm.ofBodyItems rest) hssRun)
                    | .ok st₁ .quit =>
                        have hr : r = .ok st₁ .quit := by
                          simpa [hss] using h.symm
                        cases hr
                        have hssRun := prev.stmts st ss (.ok st₁ .quit) hss
                          (by simp [ResultNotFuel])
                        simpa [evalToBodyOutcome] using
                          (BodyRuns.lift_control_to_append
                            (rest := BodyTerm.ofBodyItems rest) hssRun)
                    | .outOfFuel st₁ =>
                        have hr : r = .outOfFuel st₁ := by
                          simpa [hss] using h.symm
                        cases hr
                        cases hnf
                    | .runtimeError st₁ msg =>
                        have hr : r = .runtimeError st₁ msg := by
                          simpa [hss] using h.symm
                        cases hr
                        have hssRun := prev.stmts st ss (.runtimeError st₁ msg) hss
                          (by simp [ResultNotFuel])
                        simpa [evalToBodyOutcome] using
                          (BodyRuns.lift_error_to_append
                            (rest := BodyTerm.ofBodyItems rest) hssRun)

theorem evalExpr_to_ExprRuns {fuel st e r}
    (h : evalExpr fuel st e = r) (hnf : EvalResultNotFuel r) :
    ExprRuns st (ExprTerm.ofExpr e) (evalToExprOutcome r) :=
  (forwardProps fuel).expr st e r h hnf

theorem evalArgValues_to_ArgsRuns {fuel st args r}
    (h : evalArgValues fuel st args = r) (hnf : EvalResultNotFuel r) :
    ArgsRuns st (ArgTerm.ofArgs args) (evalToArgsOutcome r) :=
  (forwardProps fuel).args st args r h hnf

theorem evalStmt_to_StmtRuns {fuel st stmt r}
    (h : evalStmt fuel st stmt = r) (hnf : ResultNotFuel r) :
    StmtRuns st (StmtTerm.ofStmt stmt) (evalToStmtOutcome r) :=
  (forwardProps fuel).stmt st stmt r h hnf

theorem evalFor_to_StmtRuns {fuel st cond update body r}
    (h : evalFor fuel st cond update body = r) (hnf : ResultNotFuel r) :
    StmtRuns st (.forCheck cond (ExprTerm.ofExpr cond) update (StmtTerm.ofStmt body))
      (evalToStmtOutcome r) :=
  (forwardProps fuel).forLoop st cond update body r h hnf

theorem evalStmts_to_BodyRuns {fuel st stmts r}
    (h : evalStmts fuel st stmts = r) (hnf : ResultNotFuel r) :
    BodyRuns st (.stmts (StmtTerm.ofStmts stmts)) (evalToBodyOutcome r) :=
  (forwardProps fuel).stmts st stmts r h hnf

theorem evalBody_to_BodyRuns {fuel st body r}
    (h : evalBody fuel st body = r) (hnf : ResultNotFuel r) :
    BodyRuns st (BodyTerm.ofBody body) (evalToBodyOutcome r) :=
  (forwardProps fuel).body st body r h hnf

end BigSmall

end Bc
