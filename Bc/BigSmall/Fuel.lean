/-
  Fuel-bounded small-step runners used in the big↔small simulation proof.
-/

import Bc.SmallStep

namespace Bc

namespace BigSmall

open SmallStep

/-- Same principle as Mathlib/poison-lang `Nat.strong_induction_on`; bc-lean uses core `Nat.strongRecOn`. -/
theorem Nat.strong_induction_on {p : Nat → Prop} (n : Nat)
    (ind : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
  Nat.strongRecOn n ind

/-- Run `stepExpr` until a final expression outcome or fuel runs out. -/
def runExprFuel : Nat → RuntimeState → ExprTerm → ExprOutcome
  | 0, st, _ => .runtimeError st "out of fuel in runExprFuel"
  | fuel + 1, st, e =>
      match stepExpr st e with
      | .next st' e' => runExprFuel fuel st' e'
      | o => o

/-- Run `stepLVal` until a target or final outcome. -/
def runLValFuel : Nat → RuntimeState → LValTerm → LValOutcome
  | 0, st, _ => .runtimeError st "out of fuel in runLValFuel"
  | fuel + 1, st, lv =>
      match stepLVal st lv with
      | .next st' lv' => runLValFuel fuel st' lv'
      | o => o

/-- Run `stepArgs` until values or final outcome. -/
def runArgsFuel : Nat → RuntimeState → List ArgTerm → ArgListOutcome
  | 0, st, _ => .runtimeError st "out of fuel in runArgsFuel"
  | fuel + 1, st, args =>
      match stepArgs st args with
      | .next st' args' => runArgsFuel fuel st' args'
      | o => o

/-- Run `stepStmt` until done or final outcome. -/
def runStmtFuel : Nat → RuntimeState → StmtTerm → StmtOutcome
  | 0, st, _ => .runtimeError st "out of fuel in runStmtFuel"
  | fuel + 1, st, s =>
      match stepStmt st s with
      | .next st' s' => runStmtFuel fuel st' s'
      | o => o

/-- Run `stepBody` until done or final outcome. -/
def runBodyFuel : Nat → RuntimeState → BodyTerm → BodyOutcome
  | 0, st, _ => .runtimeError st "out of fuel in runBodyFuel"
  | fuel + 1, st, body =>
      match stepBody st body with
      | .next st' body' => runBodyFuel fuel st' body'
      | o => o

theorem runExprFuel_succ (fuel st e) :
    runExprFuel (fuel + 1) st e =
      match stepExpr st e with
      | .next st' e' => runExprFuel fuel st' e'
      | o => o := rfl

theorem runStmtFuel_succ (fuel st s) :
    runStmtFuel (fuel + 1) st s =
      match stepStmt st s with
      | .next st' s' => runStmtFuel fuel st' s'
      | o => o := rfl

theorem runBodyFuel_succ (fuel st body) :
    runBodyFuel (fuel + 1) st body =
      match stepBody st body with
      | .next st' body' => runBodyFuel fuel st' body'
      | o => o := rfl

end BigSmall

end Bc
