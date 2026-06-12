/-
  Adequacy of the declarative small-step relation against the executable steppers.

  Proves soundness (every derivable step matches `step`) and completeness (every
  executable step is derivable), yielding equivalence and determinism of `StepProg`.
-/

import Bc.SmallStep
import Bc.SmallStepRel

namespace Bc

namespace SmallStep

def ExprTerm.isValue : ExprTerm → Bool
  | .value _ => true
  | _ => false

def LValTerm.isTarget : LValTerm → Bool
  | .target _ => true
  | _ => false

def StmtTerm.isDone : StmtTerm → Bool
  | .done => true
  | _ => false

/-! ### Inversion: resolved forms are normal forms -/

private theorem StepExpr.not_value {st v o} : ¬ StepExpr st (.value v) o := by
  intro h; cases h

private theorem StepLVal.not_target {st t o} : ¬ StepLVal st (.target t) o := by
  intro h; cases h

private theorem StepExpr.not_isValue {st index o} (h : StepExpr st index o) :
    ExprTerm.isValue index = false := by
  cases index <;> first | rfl | exact absurd h StepExpr.not_value

private theorem StepLVal.not_isTarget {st target o} (h : StepLVal st target o) :
    LValTerm.isTarget target = false := by
  cases target <;> first | rfl | exact absurd h StepLVal.not_target

/-- Reduction lemma for expression congruences: a non-value subterm makes the
    executable take the matching expression-context branch. -/
private theorem stepExpr_arrayAccess_eq {st name index} (h : ExprTerm.isValue index = false) :
    stepExpr st (.arrayAccess name index) =
      liftE (fun e => .arrayAccess name e) (stepExpr st index) := by
  cases index <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepExpr_assignTarget_eq {st target op rhs} (h : ExprTerm.isValue rhs = false) :
    stepExpr st (.assignTarget target op rhs) =
      liftE (fun e => .assignTarget target op e) (stepExpr st rhs) := by
  cases rhs <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepExpr_relRhs_eq {st left op rhs tail} (h : ExprTerm.isValue rhs = false) :
    stepExpr st (.rel (.value left) ((op, rhs) :: tail)) =
      liftE (fun e => .rel (.value left) ((op, e) :: tail)) (stepExpr st rhs) := by
  cases rhs <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepExpr_relFirst_eq {st first rest} (h : ExprTerm.isValue first = false) :
    stepExpr st (.rel first rest) = liftE (fun e => .rel e rest) (stepExpr st first) := by
  cases first <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepExpr_binR_eq {st op left rhs} (h : ExprTerm.isValue rhs = false) :
    stepExpr st (.bin op (.value left) rhs) =
      liftE (fun e => .bin op (.value left) e) (stepExpr st rhs) := by
  cases rhs <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepExpr_binL_eq {st op lhs rhs} (h : ExprTerm.isValue lhs = false) :
    stepExpr st (.bin op lhs rhs) = liftE (fun e => .bin op e rhs) (stepExpr st lhs) := by
  cases lhs <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepExpr_neg_eq {st arg} (h : ExprTerm.isValue arg = false) :
    stepExpr st (.neg arg) = liftE (fun e => .neg e) (stepExpr st arg) := by
  cases arg <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepExpr_builtin_eq {st fn arg} (h : ExprTerm.isValue arg = false) :
    stepExpr st (.builtin fn (some arg)) =
      liftE (fun e => .builtin fn (some e)) (stepExpr st arg) := by
  cases arg <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepExpr_paren_eq {st body} (h : ExprTerm.isValue body = false) :
    stepExpr st (.paren body) = liftE (fun e => .paren e) (stepExpr st body) := by
  cases body <;> first | rfl | simp_all [ExprTerm.isValue]

/-- Reduction lemma for expression contexts over lvalues: a non-target lvalue
    makes the executable take the matching lvalue-context branch. -/
private theorem stepExpr_assign_eq {st lhs op rhs} (h : LValTerm.isTarget lhs = false) :
    stepExpr st (.assign lhs op rhs) =
      liftLE (fun lv => .assign lv op rhs) (fun st t => .next st (.assignTarget t op rhs))
        (stepLVal st lhs) := by
  cases lhs <;> first | rfl | simp_all [LValTerm.isTarget]

private theorem stepExpr_bump_eq {st op target} (h : LValTerm.isTarget target = false) :
    stepExpr st (.bump op target) =
      liftLE (fun lv => .bump op lv) (fun st t => .next st (.bump op (.target t)))
        (stepLVal st target) := by
  cases target <;> first | rfl | simp_all [LValTerm.isTarget]

/-- Reduction lemma for the lvalue-array congruence: a non-value index makes the
    executable take the congruence branch, matching `liftIndexLVal`. -/
private theorem stepLVal_array_eq {st name index} (h : ExprTerm.isValue index = false) :
    stepLVal st (.array name index) = liftIndexLVal name (stepExpr st index) := by
  cases index <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepArgs_expr_eq {st expr rest} (h : ExprTerm.isValue expr = false) :
    stepArgs st (.expr expr :: rest) =
      liftExprArgs (fun e => .expr e :: rest) (stepExpr st expr) := by
  cases expr <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepStmt_expr_eq {st original expr} (h : ExprTerm.isValue expr = false) :
    stepStmt st (.expr original expr) =
      liftExprStmt (fun e => .expr original e) (stepExpr st expr) := by
  cases expr <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepStmt_eval_eq {st expr} (h : ExprTerm.isValue expr = false) :
    stepStmt st (.eval expr) = liftExprStmt (fun e => .eval e) (stepExpr st expr) := by
  cases expr <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepStmt_ifThen_eq {st cond thenBranch} (h : ExprTerm.isValue cond = false) :
    stepStmt st (.ifThen cond thenBranch) =
      liftExprStmt (fun e => .ifThen e thenBranch) (stepExpr st cond) := by
  cases cond <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepStmt_while_eq {st condSource cond body} (h : ExprTerm.isValue cond = false) :
    stepStmt st (.while condSource cond body) =
      liftExprStmt (fun e => .while condSource e body) (stepExpr st cond) := by
  cases cond <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepStmt_forCheck_eq {st condSource cond updateSource body}
    (h : ExprTerm.isValue cond = false) :
    stepStmt st (.forCheck condSource cond updateSource body) =
      liftExprStmt (fun e => .forCheck condSource e updateSource body) (stepExpr st cond) := by
  cases cond <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepStmt_forUpdate_eq {st condSource updateSource update body}
    (h : ExprTerm.isValue update = false) :
    stepStmt st (.forUpdate condSource updateSource update body) =
      liftExprStmt (fun e => .forUpdate condSource updateSource e body)
        (stepExpr st update) := by
  cases update <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepStmt_return_eq {st expr} (h : ExprTerm.isValue expr = false) :
    stepStmt st (.return (some expr)) =
      liftExprStmt (fun e => .return (some e)) (stepExpr st expr) := by
  cases expr <;> first | rfl | simp_all [ExprTerm.isValue]

private theorem stepStmt_loopBody_eq {st body after} (h : body ≠ .done) :
    stepStmt st (.loopBody body after) = liftLoopBody after (stepStmt st body) := by
  cases body <;> first | contradiction | rfl

private theorem stepStmt_seq_eq {st first second} (h : first ≠ .done) :
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


private theorem stepExpr_sound {st e o} (h : StepExpr st e o) : stepExpr st e = o := by
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

private theorem stepLVal_sound {st lv o} (h : StepLVal st lv o) : stepLVal st lv = o := by
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

private theorem stepArgs_sound {st a o} (h : StepArgs st a o) : stepArgs st a = o := by
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

private theorem stepStmt_sound {st s o} (h : StepStmt st s o) : stepStmt st s = o := by
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

private theorem stepBody_sound {st b o} (h : StepBody st b o) : stepBody st b = o := by
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
