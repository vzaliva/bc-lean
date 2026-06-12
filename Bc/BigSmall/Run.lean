/-
  Fuel-insensitive finite-run closures for the executable small-step steppers.

  These relations are proof-only infrastructure: they describe that a stepper
  reaches a final outcome in finitely many executable steps.  The lemmas at the
  bottom connect them back to the fuel-bounded runners used by the public API.
-/

import Bc.BigSmall.Fuel

namespace Bc

namespace BigSmall

open SmallStep

def ExprFinal : ExprOutcome → Prop
  | .next _ _ => False
  | _ => True

def LValFinal : LValOutcome → Prop
  | .next _ _ => False
  | _ => True

def ArgsFinal : ArgListOutcome → Prop
  | .next _ _ => False
  | _ => True

def StmtFinal : StmtOutcome → Prop
  | .next _ _ => False
  | _ => True

def BodyFinal : BodyOutcome → Prop
  | .next _ _ => False
  | _ => True

def StepResultFinal : StepResult → Prop
  | .next _ => False
  | _ => True

inductive ExprRuns : RuntimeState → ExprTerm → ExprOutcome → Prop where
  | value {st v} :
      ExprRuns st (.value v) (.value st v)
  | control {st e st' c} :
      stepExpr st e = .control st' c → ExprRuns st e (.control st' c)
  | runtimeError {st e st' msg} :
      stepExpr st e = .runtimeError st' msg → ExprRuns st e (.runtimeError st' msg)
  | next {st e st' e' o} :
      stepExpr st e = .next st' e' → ExprRuns st' e' o → ExprRuns st e o

inductive LValRuns : RuntimeState → LValTerm → LValOutcome → Prop where
  | target {st target} :
      LValRuns st (.target target) (.target st target)
  | runtimeError {st lv st' msg} :
      stepLVal st lv = .runtimeError st' msg → LValRuns st lv (.runtimeError st' msg)
  | next {st lv st' lv' o} :
      stepLVal st lv = .next st' lv' → LValRuns st' lv' o → LValRuns st lv o

inductive ArgsRuns : RuntimeState → List ArgTerm → ArgListOutcome → Prop where
  | stop {st args o} :
      stepArgs st args = o → ArgsFinal o → ArgsRuns st args o
  | next {st args st' args' o} :
      stepArgs st args = .next st' args' → ArgsRuns st' args' o → ArgsRuns st args o

inductive StmtRuns : RuntimeState → StmtTerm → StmtOutcome → Prop where
  | stop {st s o} :
      stepStmt st s = o → StmtFinal o → StmtRuns st s o
  | next {st s st' s' o} :
      stepStmt st s = .next st' s' → StmtRuns st' s' o → StmtRuns st s o

inductive BodyRuns : RuntimeState → BodyTerm → BodyOutcome → Prop where
  | stop {st b o} :
      stepBody st b = o → BodyFinal o → BodyRuns st b o
  | next {st b st' b' o} :
      stepBody st b = .next st' b' → BodyRuns st' b' o → BodyRuns st b o

inductive ConfigRuns : Config → StepResult → Prop where
  | stop {c o} :
      step c = o → StepResultFinal o → ConfigRuns c o
  | next {c c' o} :
      step c = .next c' → ConfigRuns c' o → ConfigRuns c o

def stepResultToRunResult : StepResult → RunResult
  | .next c => .outOfFuel c.state
  | .done st => .success st
  | .control st .normal => .success st
  | .control st .quit => .success st
  | .control st .break => .runtimeError st "Break outside a loop"
  | .control st (.return _) => .runtimeError st "Return outside of a function"
  | .runtimeError st msg => .runtimeError st msg

private theorem runExprFuel_one_stop {st e o}
    (hstep : stepExpr st e = o) (hfinal : ExprFinal o) :
    runExprFuel 1 st e = o := by
  cases o <;> try cases hfinal <;> simp [runExprFuel, hstep]

private theorem runLValFuel_one_stop {st lv o}
    (hstep : stepLVal st lv = o) (hfinal : LValFinal o) :
    runLValFuel 1 st lv = o := by
  cases o <;> try cases hfinal <;> simp [runLValFuel, hstep]

private theorem runArgsFuel_one_stop {st args o}
    (hstep : stepArgs st args = o) (hfinal : ArgsFinal o) :
    runArgsFuel 1 st args = o := by
  cases o <;> try cases hfinal <;> simp [runArgsFuel, hstep]

private theorem runStmtFuel_one_stop {st s o}
    (hstep : stepStmt st s = o) (hfinal : StmtFinal o) :
    runStmtFuel 1 st s = o := by
  cases o <;> try cases hfinal <;> simp [runStmtFuel, hstep]

private theorem runBodyFuel_one_stop {st b o}
    (hstep : stepBody st b = o) (hfinal : BodyFinal o) :
    runBodyFuel 1 st b = o := by
  cases o <;> try cases hfinal <;> simp [runBodyFuel, hstep]

private theorem runConfig_one_stop {c o}
    (hstep : step c = o) (hfinal : StepResultFinal o) :
    runConfig 1 c = stepResultToRunResult o := by
  cases o with
  | next c' => cases hfinal
  | done st => simp [runConfig, hstep, stepResultToRunResult]
  | control st control =>
      cases control <;> simp [runConfig, hstep, stepResultToRunResult]
  | runtimeError st msg => simp [runConfig, hstep, stepResultToRunResult]

theorem ExprRuns.to_fuel {st e o} (h : ExprRuns st e o) :
    ∃ fuel, runExprFuel fuel st e = o := by
  induction h with
  | value =>
      exact ⟨1, by simp [runExprFuel, stepExpr]⟩
  | control hstep =>
      exact ⟨1, by simp [runExprFuel, hstep]⟩
  | runtimeError hstep =>
      exact ⟨1, by simp [runExprFuel, hstep]⟩
  | next hstep _ ih =>
      rcases ih with ⟨fuel, hfuel⟩
      exact ⟨fuel + 1, by simp [runExprFuel, hstep, hfuel]⟩

theorem LValRuns.to_fuel {st lv o} (h : LValRuns st lv o) :
    ∃ fuel, runLValFuel fuel st lv = o := by
  induction h with
  | target =>
      exact ⟨1, by simp [runLValFuel, stepLVal]⟩
  | runtimeError hstep =>
      exact ⟨1, by simp [runLValFuel, hstep]⟩
  | next hstep _ ih =>
      rcases ih with ⟨fuel, hfuel⟩
      exact ⟨fuel + 1, by simp [runLValFuel, hstep, hfuel]⟩

theorem ArgsRuns.to_fuel {st args o} (h : ArgsRuns st args o) :
    ∃ fuel, runArgsFuel fuel st args = o := by
  induction h with
  | stop hstep hfinal =>
      exact ⟨1, runArgsFuel_one_stop hstep hfinal⟩
  | next hstep _ ih =>
      rcases ih with ⟨fuel, hfuel⟩
      exact ⟨fuel + 1, by simp [runArgsFuel, hstep, hfuel]⟩

theorem StmtRuns.to_fuel {st s o} (h : StmtRuns st s o) :
    ∃ fuel, runStmtFuel fuel st s = o := by
  induction h with
  | stop hstep hfinal =>
      exact ⟨1, runStmtFuel_one_stop hstep hfinal⟩
  | next hstep _ ih =>
      rcases ih with ⟨fuel, hfuel⟩
      exact ⟨fuel + 1, by simp [runStmtFuel, hstep, hfuel]⟩

theorem BodyRuns.to_fuel {st b o} (h : BodyRuns st b o) :
    ∃ fuel, runBodyFuel fuel st b = o := by
  induction h with
  | stop hstep hfinal =>
      exact ⟨1, runBodyFuel_one_stop hstep hfinal⟩
  | next hstep _ ih =>
      rcases ih with ⟨fuel, hfuel⟩
      exact ⟨fuel + 1, by simp [runBodyFuel, hstep, hfuel]⟩

theorem ConfigRuns.to_fuel {c o} (h : ConfigRuns c o) :
    ∃ fuel, runConfig fuel c = stepResultToRunResult o := by
  induction h with
  | stop hstep hfinal =>
      exact ⟨1, runConfig_one_stop hstep hfinal⟩
  | next hstep _ ih =>
      rcases ih with ⟨fuel, hfuel⟩
      exact ⟨fuel + 1, by simp [runConfig, hstep, hfuel]⟩

theorem ArgsRuns.of_fuel {fuel st args o}
    (h : runArgsFuel fuel st args = o)
    (hfinal : ∀ st₀, o ≠ .runtimeError st₀ "out of fuel in runArgsFuel") :
    ArgsRuns st args o := by
  induction fuel generalizing st args o with
  | zero =>
      simp [runArgsFuel] at h
      exact False.elim (hfinal st h.symm)
  | succ fuel' ih =>
      cases hstep : stepArgs st args with
      | next st' args' =>
          exact ArgsRuns.next hstep (ih (by simpa [runArgsFuel, hstep] using h) hfinal)
      | values st' values =>
          have ho : runArgsFuel (fuel' + 1) st args = .values st' values := by
            simp [runArgsFuel, hstep]
          have hov : o = .values st' values := h.symm.trans ho
          rw [hov]
          exact ArgsRuns.stop hstep (by simp [ArgsFinal])
      | control st' control =>
          have ho : runArgsFuel (fuel' + 1) st args = .control st' control := by
            simp [runArgsFuel, hstep]
          have hov : o = .control st' control := h.symm.trans ho
          rw [hov]
          exact ArgsRuns.stop hstep (by simp [ArgsFinal])
      | runtimeError st' msg =>
          have ho : runArgsFuel (fuel' + 1) st args = .runtimeError st' msg := by
            simp [runArgsFuel, hstep]
          have hov : o = .runtimeError st' msg := h.symm.trans ho
          rw [hov]
          exact ArgsRuns.stop hstep (by simp [ArgsFinal])

theorem StmtRuns.of_fuel {fuel st s o}
    (h : runStmtFuel fuel st s = o)
    (hfinal : ∀ st₀, o ≠ .runtimeError st₀ "out of fuel in runStmtFuel") :
    StmtRuns st s o := by
  induction fuel generalizing st s o with
  | zero =>
      simp [runStmtFuel] at h
      exact False.elim (hfinal st h.symm)
  | succ fuel' ih =>
      cases hstep : stepStmt st s with
      | next st' s' =>
          exact StmtRuns.next hstep (ih (by simpa [runStmtFuel, hstep] using h) hfinal)
      | done st' =>
          have ho : runStmtFuel (fuel' + 1) st s = .done st' := by
            simp [runStmtFuel, hstep]
          have hov : o = .done st' := h.symm.trans ho
          rw [hov]
          exact StmtRuns.stop hstep (by simp [StmtFinal])
      | control st' control =>
          have ho : runStmtFuel (fuel' + 1) st s = .control st' control := by
            simp [runStmtFuel, hstep]
          have hov : o = .control st' control := h.symm.trans ho
          rw [hov]
          exact StmtRuns.stop hstep (by simp [StmtFinal])
      | runtimeError st' msg =>
          have ho : runStmtFuel (fuel' + 1) st s = .runtimeError st' msg := by
            simp [runStmtFuel, hstep]
          have hov : o = .runtimeError st' msg := h.symm.trans ho
          rw [hov]
          exact StmtRuns.stop hstep (by simp [StmtFinal])

theorem BodyRuns.of_fuel {fuel st b o}
    (h : runBodyFuel fuel st b = o)
    (hfinal : ∀ st₀, o ≠ .runtimeError st₀ "out of fuel in runBodyFuel") :
    BodyRuns st b o := by
  induction fuel generalizing st b o with
  | zero =>
      simp [runBodyFuel] at h
      exact False.elim (hfinal st h.symm)
  | succ fuel' ih =>
      cases hstep : stepBody st b with
      | next st' b' =>
          exact BodyRuns.next hstep (ih (by simpa [runBodyFuel, hstep] using h) hfinal)
      | done st' =>
          have ho : runBodyFuel (fuel' + 1) st b = .done st' := by
            simp [runBodyFuel, hstep]
          have hov : o = .done st' := h.symm.trans ho
          rw [hov]
          exact BodyRuns.stop hstep (by simp [BodyFinal])
      | control st' control =>
          have ho : runBodyFuel (fuel' + 1) st b = .control st' control := by
            simp [runBodyFuel, hstep]
          have hov : o = .control st' control := h.symm.trans ho
          rw [hov]
          exact BodyRuns.stop hstep (by simp [BodyFinal])
      | runtimeError st' msg =>
          have ho : runBodyFuel (fuel' + 1) st b = .runtimeError st' msg := by
            simp [runBodyFuel, hstep]
          have hov : o = .runtimeError st' msg := h.symm.trans ho
          rw [hov]
          exact BodyRuns.stop hstep (by simp [BodyFinal])

theorem ConfigRuns.of_fuel {fuel c r}
    (h : runConfig fuel c = r) (hfinal : ∀ st₀, r ≠ .outOfFuel st₀) :
    ∃ o, ConfigRuns c o ∧ stepResultToRunResult o = r := by
  induction fuel generalizing c r with
  | zero =>
      simp [runConfig] at h
      exact False.elim (hfinal c.state h.symm)
  | succ fuel' ih =>
      cases hstep : step c with
      | next c' =>
          rcases ih (by simpa [runConfig, hstep] using h) hfinal with ⟨o, hrun, hout⟩
          exact ⟨o, ConfigRuns.next hstep hrun, hout⟩
      | done st =>
          exact ⟨.done st, ConfigRuns.stop hstep (by simp [StepResultFinal]),
            by simpa [runConfig, hstep, stepResultToRunResult] using h⟩
      | control st control =>
          cases control <;>
            exact ⟨.control st _, ConfigRuns.stop hstep (by simp [StepResultFinal]),
              by simpa [runConfig, hstep, stepResultToRunResult] using h⟩
      | runtimeError st msg =>
          exact ⟨.runtimeError st msg, ConfigRuns.stop hstep (by simp [StepResultFinal]),
            by simpa [runConfig, hstep, stepResultToRunResult] using h⟩

/-! ### Context lifting for finite runs -/

theorem ExprRuns.lift_value {k : ExprTerm → ExprTerm}
    (hnext : ∀ {st e st' e'}, stepExpr st e = .next st' e' →
      stepExpr st (k e) = .next st' (k e'))
    {st e st' v o}
    (h : ExprRuns st e (.value st' v))
    (hcont : ExprRuns st' (k (.value v)) o) :
    ExprRuns st (k e) o := by
  generalize hout : ExprOutcome.value st' v = out at h
  induction h with
  | value =>
      cases hout
      exact hcont
  | control _ => cases hout
  | runtimeError _ => cases hout
  | next hstep _ ih =>
      exact ExprRuns.next (hnext hstep) (ih hout)

theorem ExprRuns.lift_control {k : ExprTerm → ExprTerm}
    (hnext : ∀ {st e st' e'}, stepExpr st e = .next st' e' →
      stepExpr st (k e) = .next st' (k e'))
    (hcontrol : ∀ {st e st' c}, stepExpr st e = .control st' c →
      stepExpr st (k e) = .control st' c)
    {st e st' c}
    (h : ExprRuns st e (.control st' c)) :
    ExprRuns st (k e) (.control st' c) := by
  generalize hout : ExprOutcome.control st' c = out at h
  induction h with
  | value => cases hout
  | control hstep =>
      cases hout
      exact ExprRuns.control (hcontrol hstep)
  | runtimeError _ => cases hout
  | next hstep _ ih => exact ExprRuns.next (hnext hstep) (ih hout)

theorem ExprRuns.lift_error {k : ExprTerm → ExprTerm}
    (hnext : ∀ {st e st' e'}, stepExpr st e = .next st' e' →
      stepExpr st (k e) = .next st' (k e'))
    (herror : ∀ {st e st' msg}, stepExpr st e = .runtimeError st' msg →
      stepExpr st (k e) = .runtimeError st' msg)
    {st e st' msg}
    (h : ExprRuns st e (.runtimeError st' msg)) :
    ExprRuns st (k e) (.runtimeError st' msg) := by
  generalize hout : ExprOutcome.runtimeError st' msg = out at h
  induction h with
  | value => cases hout
  | control _ => cases hout
  | runtimeError hstep =>
      cases hout
      exact ExprRuns.runtimeError (herror hstep)
  | next hstep _ ih => exact ExprRuns.next (hnext hstep) (ih hout)

theorem ExprRuns.lift_value_to_lval {k : ExprTerm → LValTerm}
    (hnext : ∀ {st e st' e'}, stepExpr st e = .next st' e' →
      stepLVal st (k e) = .next st' (k e'))
    {st e st' v o}
    (h : ExprRuns st e (.value st' v))
    (hcont : LValRuns st' (k (.value v)) o) :
    LValRuns st (k e) o := by
  generalize hout : ExprOutcome.value st' v = out at h
  induction h with
  | value =>
      cases hout
      exact hcont
  | control _ => cases hout
  | runtimeError _ => cases hout
  | next hstep _ ih =>
      exact LValRuns.next (hnext hstep) (ih hout)

theorem ExprRuns.lift_control_to_lval {k : ExprTerm → LValTerm}
    (hnext : ∀ {st e st' e'}, stepExpr st e = .next st' e' →
      stepLVal st (k e) = .next st' (k e'))
    (hcontrol : ∀ {st e st' c}, stepExpr st e = .control st' c →
      stepLVal st (k e) = .runtimeError st' "control escaped from lvalue evaluation")
    {st e st' c}
    (h : ExprRuns st e (.control st' c)) :
    LValRuns st (k e) (.runtimeError st' "control escaped from lvalue evaluation") := by
  generalize hout : ExprOutcome.control st' c = out at h
  induction h with
  | value => cases hout
  | control hstep =>
      cases hout
      exact LValRuns.runtimeError (hcontrol hstep)
  | runtimeError _ => cases hout
  | next hstep _ ih => exact LValRuns.next (hnext hstep) (ih hout)

theorem ExprRuns.lift_error_to_lval {k : ExprTerm → LValTerm}
    (hnext : ∀ {st e st' e'}, stepExpr st e = .next st' e' →
      stepLVal st (k e) = .next st' (k e'))
    (herror : ∀ {st e st' msg}, stepExpr st e = .runtimeError st' msg →
      stepLVal st (k e) = .runtimeError st' msg)
    {st e st' msg}
    (h : ExprRuns st e (.runtimeError st' msg)) :
    LValRuns st (k e) (.runtimeError st' msg) := by
  generalize hout : ExprOutcome.runtimeError st' msg = out at h
  induction h with
  | value => cases hout
  | control _ => cases hout
  | runtimeError hstep =>
      cases hout
      exact LValRuns.runtimeError (herror hstep)
  | next hstep _ ih => exact LValRuns.next (hnext hstep) (ih hout)

theorem LValRuns.lift_target_to_expr {k : LValTerm → ExprTerm}
    (hnext : ∀ {st lv st' lv'}, stepLVal st lv = .next st' lv' →
      stepExpr st (k lv) = .next st' (k lv'))
    {st lv st' target o}
    (h : LValRuns st lv (.target st' target))
    (hcont : ExprRuns st' (k (.target target)) o) :
    ExprRuns st (k lv) o := by
  generalize hout : LValOutcome.target st' target = out at h
  induction h with
  | target =>
      cases hout
      exact hcont
  | runtimeError _ => cases hout
  | next hstep _ ih =>
      exact ExprRuns.next (hnext hstep) (ih hout)

theorem LValRuns.lift_error_to_expr {k : LValTerm → ExprTerm}
    (hnext : ∀ {st lv st' lv'}, stepLVal st lv = .next st' lv' →
      stepExpr st (k lv) = .next st' (k lv'))
    (herror : ∀ {st lv st' msg}, stepLVal st lv = .runtimeError st' msg →
      stepExpr st (k lv) = .runtimeError st' msg)
    {st lv st' msg}
    (h : LValRuns st lv (.runtimeError st' msg)) :
    ExprRuns st (k lv) (.runtimeError st' msg) := by
  generalize hout : LValOutcome.runtimeError st' msg = out at h
  induction h with
  | target => cases hout
  | runtimeError hstep =>
      cases hout
      exact ExprRuns.runtimeError (herror hstep)
  | next hstep _ ih => exact ExprRuns.next (hnext hstep) (ih hout)

theorem ArgsRuns.lift_values_to_expr {k : List ArgTerm → ExprTerm}
    (hnext : ∀ {st args st' args'}, stepArgs st args = .next st' args' →
      stepExpr st (k args) = .next st' (k args'))
    {st args st' values o}
    (hvalues : ∀ {st args st' values}, stepArgs st args = .values st' values →
      ExprRuns st (k args) o)
    (h : ArgsRuns st args (.values st' values)) :
    ExprRuns st (k args) o := by
  generalize hout : ArgListOutcome.values st' values = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact hvalues hstep
  | next hstep _ ih => exact ExprRuns.next (hnext hstep) (ih hout)

theorem ArgsRuns.lift_control_to_expr {k : List ArgTerm → ExprTerm}
    (hnext : ∀ {st args st' args'}, stepArgs st args = .next st' args' →
      stepExpr st (k args) = .next st' (k args'))
    (hcontrol : ∀ {st args st' c}, stepArgs st args = .control st' c →
      stepExpr st (k args) = .control st' c)
    {st args st' c}
    (h : ArgsRuns st args (.control st' c)) :
    ExprRuns st (k args) (.control st' c) := by
  generalize hout : ArgListOutcome.control st' c = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact ExprRuns.control (hcontrol hstep)
  | next hstep _ ih => exact ExprRuns.next (hnext hstep) (ih hout)

theorem ArgsRuns.lift_error_to_expr {k : List ArgTerm → ExprTerm}
    (hnext : ∀ {st args st' args'}, stepArgs st args = .next st' args' →
      stepExpr st (k args) = .next st' (k args'))
    (herror : ∀ {st args st' msg}, stepArgs st args = .runtimeError st' msg →
      stepExpr st (k args) = .runtimeError st' msg)
    {st args st' msg}
    (h : ArgsRuns st args (.runtimeError st' msg)) :
    ExprRuns st (k args) (.runtimeError st' msg) := by
  generalize hout : ArgListOutcome.runtimeError st' msg = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact ExprRuns.runtimeError (herror hstep)
  | next hstep _ ih => exact ExprRuns.next (hnext hstep) (ih hout)

theorem ExprRuns.lift_value_to_args {k : ExprTerm → List ArgTerm}
    (hnext : ∀ {st e st' e'}, stepExpr st e = .next st' e' →
      stepArgs st (k e) = .next st' (k e'))
    {st e st' v o}
    (h : ExprRuns st e (.value st' v))
    (hcont : ArgsRuns st' (k (.value v)) o) :
    ArgsRuns st (k e) o := by
  generalize hout : ExprOutcome.value st' v = out at h
  induction h with
  | value =>
      cases hout
      exact hcont
  | control _ => cases hout
  | runtimeError _ => cases hout
  | next hstep _ ih =>
      exact ArgsRuns.next (hnext hstep) (ih hout)

theorem ExprRuns.lift_control_to_args {k : ExprTerm → List ArgTerm}
    (hnext : ∀ {st e st' e'}, stepExpr st e = .next st' e' →
      stepArgs st (k e) = .next st' (k e'))
    (hcontrol : ∀ {st e st' c}, stepExpr st e = .control st' c →
      stepArgs st (k e) = .control st' c)
    {st e st' c}
    (h : ExprRuns st e (.control st' c)) :
    ArgsRuns st (k e) (.control st' c) := by
  generalize hout : ExprOutcome.control st' c = out at h
  induction h with
  | value => cases hout
  | control hstep =>
      cases hout
      exact ArgsRuns.stop (hcontrol hstep) (by simp [ArgsFinal])
  | runtimeError _ => cases hout
  | next hstep _ ih => exact ArgsRuns.next (hnext hstep) (ih hout)

theorem ExprRuns.lift_error_to_args {k : ExprTerm → List ArgTerm}
    (hnext : ∀ {st e st' e'}, stepExpr st e = .next st' e' →
      stepArgs st (k e) = .next st' (k e'))
    (herror : ∀ {st e st' msg}, stepExpr st e = .runtimeError st' msg →
      stepArgs st (k e) = .runtimeError st' msg)
    {st e st' msg}
    (h : ExprRuns st e (.runtimeError st' msg)) :
    ArgsRuns st (k e) (.runtimeError st' msg) := by
  generalize hout : ExprOutcome.runtimeError st' msg = out at h
  induction h with
  | value => cases hout
  | control _ => cases hout
  | runtimeError hstep =>
      cases hout
      exact ArgsRuns.stop (herror hstep) (by simp [ArgsFinal])
  | next hstep _ ih => exact ArgsRuns.next (hnext hstep) (ih hout)

theorem ArgsRuns.lift_tail_values {k : List ArgTerm → List ArgTerm}
    (kv : List (Sum Num Name) → List (Sum Num Name))
    (hnext : ∀ {st args st' args'}, stepArgs st args = .next st' args' →
      stepArgs st (k args) = .next st' (k args'))
    (hvalues : ∀ {st args st' values}, stepArgs st args = .values st' values →
      stepArgs st (k args) = .values st' (kv values))
    {st args st' values}
    (h : ArgsRuns st args (.values st' values)) :
    ArgsRuns st (k args) (.values st' (kv values)) := by
  generalize hout : ArgListOutcome.values st' values = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact ArgsRuns.stop (hvalues hstep) (by simp [ArgsFinal])
  | next hstep _ ih => exact ArgsRuns.next (hnext hstep) (ih hout)

theorem ArgsRuns.lift_tail_control {k : List ArgTerm → List ArgTerm}
    (hnext : ∀ {st args st' args'}, stepArgs st args = .next st' args' →
      stepArgs st (k args) = .next st' (k args'))
    (hcontrol : ∀ {st args st' c}, stepArgs st args = .control st' c →
      stepArgs st (k args) = .control st' c)
    {st args st' c}
    (h : ArgsRuns st args (.control st' c)) :
    ArgsRuns st (k args) (.control st' c) := by
  generalize hout : ArgListOutcome.control st' c = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact ArgsRuns.stop (hcontrol hstep) (by simp [ArgsFinal])
  | next hstep _ ih => exact ArgsRuns.next (hnext hstep) (ih hout)

theorem ArgsRuns.lift_tail_error {k : List ArgTerm → List ArgTerm}
    (hnext : ∀ {st args st' args'}, stepArgs st args = .next st' args' →
      stepArgs st (k args) = .next st' (k args'))
    (herror : ∀ {st args st' msg}, stepArgs st args = .runtimeError st' msg →
      stepArgs st (k args) = .runtimeError st' msg)
    {st args st' msg}
    (h : ArgsRuns st args (.runtimeError st' msg)) :
    ArgsRuns st (k args) (.runtimeError st' msg) := by
  generalize hout : ArgListOutcome.runtimeError st' msg = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact ArgsRuns.stop (herror hstep) (by simp [ArgsFinal])
  | next hstep _ ih => exact ArgsRuns.next (hnext hstep) (ih hout)

theorem ExprRuns.lift_value_to_stmt {k : ExprTerm → StmtTerm}
    (hnext : ∀ {st e st' e'}, stepExpr st e = .next st' e' →
      stepStmt st (k e) = .next st' (k e'))
    {st e st' v o}
    (h : ExprRuns st e (.value st' v))
    (hcont : StmtRuns st' (k (.value v)) o) :
    StmtRuns st (k e) o := by
  generalize hout : ExprOutcome.value st' v = out at h
  induction h with
  | value =>
      cases hout
      exact hcont
  | control _ => cases hout
  | runtimeError _ => cases hout
  | next hstep _ ih => exact StmtRuns.next (hnext hstep) (ih hout)

theorem ExprRuns.lift_control_to_stmt {k : ExprTerm → StmtTerm}
    (hnext : ∀ {st e st' e'}, stepExpr st e = .next st' e' →
      stepStmt st (k e) = .next st' (k e'))
    (hcontrol : ∀ {st e st' c}, stepExpr st e = .control st' c →
      stepStmt st (k e) = .control st' c)
    {st e st' c}
    (h : ExprRuns st e (.control st' c)) :
    StmtRuns st (k e) (.control st' c) := by
  generalize hout : ExprOutcome.control st' c = out at h
  induction h with
  | value => cases hout
  | control hstep =>
      cases hout
      exact StmtRuns.stop (hcontrol hstep) (by simp [StmtFinal])
  | runtimeError _ => cases hout
  | next hstep _ ih => exact StmtRuns.next (hnext hstep) (ih hout)

theorem ExprRuns.lift_error_to_stmt {k : ExprTerm → StmtTerm}
    (hnext : ∀ {st e st' e'}, stepExpr st e = .next st' e' →
      stepStmt st (k e) = .next st' (k e'))
    (herror : ∀ {st e st' msg}, stepExpr st e = .runtimeError st' msg →
      stepStmt st (k e) = .runtimeError st' msg)
    {st e st' msg}
    (h : ExprRuns st e (.runtimeError st' msg)) :
    StmtRuns st (k e) (.runtimeError st' msg) := by
  generalize hout : ExprOutcome.runtimeError st' msg = out at h
  induction h with
  | value => cases hout
  | control _ => cases hout
  | runtimeError hstep =>
      cases hout
      exact StmtRuns.stop (herror hstep) (by simp [StmtFinal])
  | next hstep _ ih => exact StmtRuns.next (hnext hstep) (ih hout)

private theorem stepStmt_seq_next {st s second st' s'}
    (hstep : stepStmt st s = .next st' s') :
    stepStmt st (.seq s second) = .next st' (.seq s' second) := by
  cases s <;> simp_all [stepStmt]

private theorem stepStmt_seq_done {st s second st'}
    (hstep : stepStmt st s = .done st') :
    stepStmt st (.seq s second) = .next st' second := by
  cases s <;> simp_all [stepStmt]

private theorem stepStmt_seq_control {st s second st' c}
    (hstep : stepStmt st s = .control st' c) :
    stepStmt st (.seq s second) = .control st' c := by
  cases s <;> simp_all [stepStmt]

private theorem stepStmt_seq_error {st s second st' msg}
    (hstep : stepStmt st s = .runtimeError st' msg) :
    stepStmt st (.seq s second) = .runtimeError st' msg := by
  cases s <;> simp_all [stepStmt]

private theorem stepStmt_loop_next {st body after st' body'}
    (hstep : stepStmt st body = .next st' body') :
    stepStmt st (.loopBody body after) = .next st' (.loopBody body' after) := by
  cases body <;> simp_all [stepStmt]

private theorem stepStmt_loop_done {st body after st'}
    (hstep : stepStmt st body = .done st') :
    stepStmt st (.loopBody body after) = .next st' after := by
  cases body <;> simp_all [stepStmt]

private theorem stepStmt_loop_break {st body after st'}
    (hstep : stepStmt st body = .control st' .break) :
    stepStmt st (.loopBody body after) = .done st' := by
  cases body <;> simp_all [stepStmt]

private theorem stepStmt_loop_control {st body after st' c}
    (hnot : c ≠ .break) (hstep : stepStmt st body = .control st' c) :
    stepStmt st (.loopBody body after) = .control st' c := by
  cases body <;> simp_all [stepStmt, hnot]

private theorem stepStmt_loop_error {st body after st' msg}
    (hstep : stepStmt st body = .runtimeError st' msg) :
    stepStmt st (.loopBody body after) = .runtimeError st' msg := by
  cases body <;> simp_all [stepStmt]

theorem StmtRuns.lift_done_to_body {rest : List StmtTerm}
    {st s st' o}
    (h : StmtRuns st s (.done st'))
    (hcont : BodyRuns st' (.stmts rest) o) :
    BodyRuns st (.stmts (s :: rest)) o := by
  generalize hout : StmtOutcome.done st' = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact BodyRuns.next (by simp [stepBody, hstep]) hcont
  | next hstep _ ih =>
      exact BodyRuns.next (by simp [stepBody, hstep]) (ih hout)

theorem StmtRuns.lift_control_to_body {rest : List StmtTerm}
    {st s st' c}
    (h : StmtRuns st s (.control st' c)) :
    BodyRuns st (.stmts (s :: rest)) (.control st' c) := by
  generalize hout : StmtOutcome.control st' c = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact BodyRuns.stop (by simp [stepBody, hstep]) (by simp [BodyFinal])
  | next hstep _ ih =>
      exact BodyRuns.next (by simp [stepBody, hstep]) (ih hout)

theorem StmtRuns.lift_error_to_body {rest : List StmtTerm}
    {st s st' msg}
    (h : StmtRuns st s (.runtimeError st' msg)) :
    BodyRuns st (.stmts (s :: rest)) (.runtimeError st' msg) := by
  generalize hout : StmtOutcome.runtimeError st' msg = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact BodyRuns.stop (by simp [stepBody, hstep]) (by simp [BodyFinal])
  | next hstep _ ih =>
      exact BodyRuns.next (by simp [stepBody, hstep]) (ih hout)

private theorem stepBody_append_next {st pre rest st' pre'}
    (hstep : stepBody st (.stmts pre) = .next st' (.stmts pre')) :
    stepBody st (.stmts (pre ++ rest)) = .next st' (.stmts (pre' ++ rest)) := by
  cases pre with
  | nil =>
      simp [stepBody] at hstep
  | cons stmt pre =>
      simp [stepBody] at hstep ⊢
      cases hstmt : stepStmt st stmt <;> simp [hstmt] at hstep ⊢
      · rcases hstep with ⟨rfl, rfl⟩
        constructor <;> rfl
      · rcases hstep with ⟨rfl, rfl⟩
        constructor <;> rfl

private theorem stepBody_append_control {st pre rest st' c}
    (hstep : stepBody st (.stmts pre) = .control st' c) :
    stepBody st (.stmts (pre ++ rest)) = .control st' c := by
  cases pre with
  | nil =>
      simp [stepBody] at hstep
  | cons stmt pre =>
      simp [stepBody] at hstep ⊢
      cases hstmt : stepStmt st stmt <;> simp [hstmt] at hstep ⊢
      rcases hstep with ⟨rfl, rfl⟩
      constructor <;> rfl

private theorem stepBody_append_error {st pre rest st' msg}
    (hstep : stepBody st (.stmts pre) = .runtimeError st' msg) :
    stepBody st (.stmts (pre ++ rest)) = .runtimeError st' msg := by
  cases pre with
  | nil =>
      simp [stepBody] at hstep
  | cons stmt pre =>
      simp [stepBody] at hstep ⊢
      cases hstmt : stepStmt st stmt <;> simp [hstmt] at hstep ⊢
      rcases hstep with ⟨rfl, rfl⟩
      constructor <;> rfl

private theorem stepBody_append_next_exists {st pre rest st' body'}
    (hstep : stepBody st (.stmts pre) = .next st' body') :
    ∃ pre', body' = .stmts pre' ∧
      stepBody st (.stmts (pre ++ rest)) = .next st' (.stmts (pre' ++ rest)) := by
  cases pre with
  | nil =>
      simp [stepBody] at hstep
  | cons stmt pre =>
      simp [stepBody] at hstep
      cases hstmt : stepStmt st stmt <;> simp [hstmt] at hstep
      · rcases hstep with ⟨rfl, rfl⟩
        exact ⟨_, rfl, by simp [stepBody, hstmt]⟩
      · rcases hstep with ⟨rfl, rfl⟩
        exact ⟨_, rfl, by simp [stepBody, hstmt]⟩

private theorem stepBody_cons_ne_done {st stmt rest st'} :
    stepBody st (.stmts (stmt :: rest)) ≠ .done st' := by
  simp [stepBody]
  cases stepStmt st stmt <;> simp

theorem BodyRuns.lift_done_to_append {rest : List StmtTerm}
    {st pre st' o}
    (h : BodyRuns st (.stmts pre) (.done st'))
    (hcont : BodyRuns st' (.stmts rest) o) :
    BodyRuns st (.stmts (pre ++ rest)) o := by
  generalize hbody : BodyTerm.stmts pre = body at h
  generalize hout : BodyOutcome.done st' = out at h
  induction h generalizing pre rest with
  | stop hstep _ =>
      cases hbody
      cases hout
      cases pre with
      | nil =>
          simp [stepBody] at hstep
          cases hstep
          simpa using hcont
      | cons stmt pre =>
          exact False.elim (stepBody_cons_ne_done hstep)
  | next hstep _ ih =>
      cases hbody
      rcases stepBody_append_next_exists (rest := rest) hstep with
        ⟨pre', hbodyNext, hstepAppend⟩
      exact BodyRuns.next hstepAppend (ih hcont hbodyNext.symm hout)

theorem BodyRuns.lift_control_to_append {rest : List StmtTerm}
    {st pre st' c}
    (h : BodyRuns st (.stmts pre) (.control st' c)) :
    BodyRuns st (.stmts (pre ++ rest)) (.control st' c) := by
  generalize hbody : BodyTerm.stmts pre = body at h
  generalize hout : BodyOutcome.control st' c = out at h
  induction h generalizing pre rest with
  | stop hstep _ =>
      cases hbody
      cases hout
      exact BodyRuns.stop (stepBody_append_control hstep) (by simp [BodyFinal])
  | next hstep _ ih =>
      cases hbody
      rcases stepBody_append_next_exists (rest := rest) hstep with
        ⟨pre', hbodyNext, hstepAppend⟩
      exact BodyRuns.next hstepAppend (ih hbodyNext.symm hout)

theorem BodyRuns.lift_error_to_append {rest : List StmtTerm}
    {st pre st' msg}
    (h : BodyRuns st (.stmts pre) (.runtimeError st' msg)) :
    BodyRuns st (.stmts (pre ++ rest)) (.runtimeError st' msg) := by
  generalize hbody : BodyTerm.stmts pre = body at h
  generalize hout : BodyOutcome.runtimeError st' msg = out at h
  induction h generalizing pre rest with
  | stop hstep _ =>
      cases hbody
      cases hout
      exact BodyRuns.stop (stepBody_append_error hstep) (by simp [BodyFinal])
  | next hstep _ ih =>
      cases hbody
      rcases stepBody_append_next_exists (rest := rest) hstep with
        ⟨pre', hbodyNext, hstepAppend⟩
      exact BodyRuns.next hstepAppend (ih hbodyNext.symm hout)

theorem StmtRuns.lift_done_to_seq {second : StmtTerm}
    {st s st' o}
    (h : StmtRuns st s (.done st'))
    (hcont : StmtRuns st' second o) :
    StmtRuns st (.seq s second) o := by
  generalize hout : StmtOutcome.done st' = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact StmtRuns.next (stepStmt_seq_done hstep) hcont
  | next hstep _ ih =>
      exact StmtRuns.next (stepStmt_seq_next hstep) (ih hout)

theorem StmtRuns.lift_control_to_seq {second : StmtTerm}
    {st s st' c}
    (h : StmtRuns st s (.control st' c)) :
    StmtRuns st (.seq s second) (.control st' c) := by
  generalize hout : StmtOutcome.control st' c = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact StmtRuns.stop (stepStmt_seq_control hstep) (by simp [StmtFinal])
  | next hstep _ ih =>
      exact StmtRuns.next (stepStmt_seq_next hstep) (ih hout)

theorem StmtRuns.lift_error_to_seq {second : StmtTerm}
    {st s st' msg}
    (h : StmtRuns st s (.runtimeError st' msg)) :
    StmtRuns st (.seq s second) (.runtimeError st' msg) := by
  generalize hout : StmtOutcome.runtimeError st' msg = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact StmtRuns.stop (stepStmt_seq_error hstep) (by simp [StmtFinal])
  | next hstep _ ih =>
      exact StmtRuns.next (stepStmt_seq_next hstep) (ih hout)

theorem StmtRuns.lift_done_to_loop {after : StmtTerm}
    {st body st' o}
    (h : StmtRuns st body (.done st'))
    (hcont : StmtRuns st' after o) :
    StmtRuns st (.loopBody body after) o := by
  generalize hout : StmtOutcome.done st' = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact StmtRuns.next (stepStmt_loop_done hstep) hcont
  | next hstep _ ih =>
      exact StmtRuns.next (stepStmt_loop_next hstep) (ih hout)

theorem StmtRuns.lift_break_to_loop {after : StmtTerm}
    {st body st'}
    (h : StmtRuns st body (.control st' .break)) :
    StmtRuns st (.loopBody body after) (.done st') := by
  generalize hout : StmtOutcome.control st' Control.break = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact StmtRuns.stop (stepStmt_loop_break hstep) (by simp [StmtFinal])
  | next hstep _ ih =>
      exact StmtRuns.next (stepStmt_loop_next hstep) (ih hout)

theorem StmtRuns.lift_control_to_loop {after : StmtTerm}
    {st body st' c}
    (hnot : c ≠ .break)
    (h : StmtRuns st body (.control st' c)) :
    StmtRuns st (.loopBody body after) (.control st' c) := by
  generalize hout : StmtOutcome.control st' c = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact StmtRuns.stop (stepStmt_loop_control hnot hstep) (by simp [StmtFinal])
  | next hstep _ ih =>
      exact StmtRuns.next (stepStmt_loop_next hstep) (ih hout)

theorem StmtRuns.lift_error_to_loop {after : StmtTerm}
    {st body st' msg}
    (h : StmtRuns st body (.runtimeError st' msg)) :
    StmtRuns st (.loopBody body after) (.runtimeError st' msg) := by
  generalize hout : StmtOutcome.runtimeError st' msg = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact StmtRuns.stop (stepStmt_loop_error hstep) (by simp [StmtFinal])
  | next hstep _ ih =>
      exact StmtRuns.next (stepStmt_loop_next hstep) (ih hout)

theorem BodyRuns.lift_done_to_block {st body st'}
    (h : BodyRuns st body (.done st')) :
    StmtRuns st (.block body) (.done st') := by
  generalize hout : BodyOutcome.done st' = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact StmtRuns.stop (by simp [stepStmt, hstep]) (by simp [StmtFinal])
  | next hstep _ ih =>
      exact StmtRuns.next (by simp [stepStmt, hstep]) (ih hout)

theorem BodyRuns.lift_control_to_block {st body st' c}
    (h : BodyRuns st body (.control st' c)) :
    StmtRuns st (.block body) (.control st' c) := by
  generalize hout : BodyOutcome.control st' c = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact StmtRuns.stop (by simp [stepStmt, hstep]) (by simp [StmtFinal])
  | next hstep _ ih =>
      exact StmtRuns.next (by simp [stepStmt, hstep]) (ih hout)

theorem BodyRuns.lift_error_to_block {st body st' msg}
    (h : BodyRuns st body (.runtimeError st' msg)) :
    StmtRuns st (.block body) (.runtimeError st' msg) := by
  generalize hout : BodyOutcome.runtimeError st' msg = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact StmtRuns.stop (by simp [stepStmt, hstep]) (by simp [StmtFinal])
  | next hstep _ ih =>
      exact StmtRuns.next (by simp [stepStmt, hstep]) (ih hout)

theorem BodyRuns.lift_done_to_activeCall {st body st'}
    (h : BodyRuns st body (.done st')) :
    ExprRuns st (.activeCall body) (.value (popFrame st') Num.zero) := by
  generalize hout : BodyOutcome.done st' = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact ExprRuns.next (by simp [stepExpr, hstep]) ExprRuns.value
  | next hstep _ ih =>
      exact ExprRuns.next (by simp [stepExpr, hstep]) (ih hout)

private def activeCallControlOutcome (st : RuntimeState) : Control → ExprOutcome
  | .normal => .value (popFrame st) Num.zero
  | .break => .runtimeError (popFrame st) "Break outside a loop"
  | .return value? => .value (popFrame st) (returnValue value?)
  | .quit => .control (popFrame st) .quit

theorem BodyRuns.lift_control_to_activeCall {st body st' c}
    (h : BodyRuns st body (.control st' c)) :
    ExprRuns st (.activeCall body) (activeCallControlOutcome st' c) := by
  generalize hout : BodyOutcome.control st' c = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      cases c <;> first
        | exact ExprRuns.next (by simp [activeCallControlOutcome, stepExpr, hstep]) ExprRuns.value
        | exact ExprRuns.runtimeError (by simp [activeCallControlOutcome, stepExpr, hstep])
        | exact ExprRuns.control (by simp [activeCallControlOutcome, stepExpr, hstep])
  | next hstep _ ih =>
      exact ExprRuns.next (by simp [stepExpr, hstep]) (ih hout)

theorem BodyRuns.lift_error_to_activeCall {st body st' msg}
    (h : BodyRuns st body (.runtimeError st' msg)) :
    ExprRuns st (.activeCall body) (.runtimeError (popFrame st') msg) := by
  generalize hout : BodyOutcome.runtimeError st' msg = out at h
  induction h with
  | stop hstep _ =>
      cases hout
      exact ExprRuns.runtimeError (by simp [stepExpr, hstep])
  | next hstep _ ih =>
      exact ExprRuns.next (by simp [stepExpr, hstep]) (ih hout)

end BigSmall

end Bc
