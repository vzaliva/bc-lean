/-
  Expression-layer bidirectional simulation between big-step `eval*` and
  fuel-bounded small-step runners.
-/

import Bc.BigSmall.Bounds
import Bc.BigStep

namespace Bc

namespace BigSmall

open SmallStep

/-! ### Outcome translation -/

def evalToExprOutcome : EvalResult Num → ExprOutcome
  | .ok st n => .value st n
  | .control st c => .control st c
  | .outOfFuel st => .runtimeError st "internal outOfFuel"
  | .runtimeError st msg => .runtimeError st msg

def evalToLValOutcome : EvalResult LValueTarget → LValOutcome
  | .ok st t => .target st t
  | .control st _ => .runtimeError st "control escaped from lvalue evaluation"
  | .outOfFuel st => .runtimeError st "internal outOfFuel"
  | .runtimeError st msg => .runtimeError st msg

def evalToArgsOutcome : EvalResult (List (Sum Num Name)) → ArgListOutcome
  | .ok st vs => .values st vs
  | .control st c => .control st c
  | .outOfFuel st => .runtimeError st "internal outOfFuel"
  | .runtimeError st msg => .runtimeError st msg

def exprFromOutcome : ExprOutcome → EvalResult Num
  | .value st n => .ok st n
  | .control st c => .control st c
  | .next _ _ => .runtimeError {} "internal next in exprFromOutcome"
  | .runtimeError st msg => .runtimeError st msg

def lvalFromOutcome : LValOutcome → EvalResult LValueTarget
  | .target st t => .ok st t
  | .next _ _ => .runtimeError {} "internal next in lvalFromOutcome"
  | .runtimeError st msg => .runtimeError st msg

def argsFromOutcome : ArgListOutcome → EvalResult (List (Sum Num Name))
  | .values st vs => .ok st vs
  | .control st c => .control st c
  | .next _ _ => .runtimeError {} "internal next in argsFromOutcome"
  | .runtimeError st msg => .runtimeError st msg

def ExprOutcome.isFinal : ExprOutcome → Bool
  | .next _ _ => false
  | _ => true

def LValOutcome.isFinal : LValOutcome → Bool
  | .next _ _ => false
  | _ => true

def ArgListOutcome.isFinal : ArgListOutcome → Bool
  | .next _ _ => false
  | _ => true

/-! ### Basic fuel-runner lemmas -/

private theorem runExprFuel_step (fuel st e) :
    runExprFuel (fuel + 1) st e =
      match stepExpr st e with
      | .next st' e' => runExprFuel fuel st' e'
      | o => o := rfl

private theorem runLValFuel_step (fuel st lv) :
    runLValFuel (fuel + 1) st lv =
      match stepLVal st lv with
      | .next st' lv' => runLValFuel fuel st' lv'
      | o => o := rfl

private theorem runArgsFuel_step (fuel st args) :
    runArgsFuel (fuel + 1) st args =
      match stepArgs st args with
      | .next st' args' => runArgsFuel fuel st' args'
      | o => o := rfl

private theorem runExprFuel_zero_out {st e} :
    runExprFuel 0 st e = .runtimeError st "out of fuel in runExprFuel" := rfl

private theorem runLValFuel_zero_out {st lv} :
    runLValFuel 0 st lv = .runtimeError st "out of fuel in runLValFuel" := rfl

private theorem runArgsFuel_zero_out {st args} :
    runArgsFuel 0 st args = .runtimeError st "out of fuel in runArgsFuel" := rfl

private theorem runExprFuel_mono {fuel₁ fuel₂ st e o}
    (hle : fuel₁ ≤ fuel₂) (h : runExprFuel fuel₁ st e = o)
    (hfinal : ∀ st₀, o ≠ .runtimeError st₀ "out of fuel in runExprFuel") :
    runExprFuel fuel₂ st e = o := by
  suffices ∀ fuel₂ fuel₀, fuel₀ ≤ fuel₂ → ∀ st e, runExprFuel fuel₀ st e = o → runExprFuel fuel₂ st e = o by
    exact this fuel₂ fuel₁ hle st e h
  intro fuel₂
  induction fuel₂ using Nat.strong_induction_on with
  | _ fuel₂ ih =>
    intro fuel₀ hle st e h
    cases fuel₂ with
    | zero =>
        cases fuel₀ with
        | zero => exact (hfinal st (Eq.symm (by simpa [runExprFuel_zero_out] using h))).elim
        | succ _ => exact absurd hle (Nat.not_succ_le_zero _)
    | succ fuel' =>
        cases fuel₀ with
        | zero => exact (hfinal st (Eq.symm (by simpa [runExprFuel_zero_out] using h))).elim
        | succ fuel₀' =>
          rw [runExprFuel_step]
          cases hstep : stepExpr st e with
          | next st' e' =>
              have hinner : runExprFuel fuel₀' st' e' = o := by
                simpa [runExprFuel_step, hstep] using h
              have hle' : fuel₀' ≤ fuel' := Nat.le_of_succ_le_succ hle
              exact ih fuel' (Nat.lt_succ_self fuel') fuel₀' hle' st' e' hinner
          | value _ _ =>
              rw [runExprFuel_step] at h
              rw [hstep] at h
              exact h
          | control _ _ =>
              rw [runExprFuel_step] at h
              rw [hstep] at h
              exact h
          | runtimeError _ _ =>
              rw [runExprFuel_step] at h
              rw [hstep] at h
              exact h

private theorem runLValFuel_mono {fuel₁ fuel₂ st lv o}
    (hle : fuel₁ ≤ fuel₂) (h : runLValFuel fuel₁ st lv = o)
    (hfinal : ∀ st₀, o ≠ .runtimeError st₀ "out of fuel in runLValFuel") :
    runLValFuel fuel₂ st lv = o := by
  suffices ∀ fuel₂ fuel₀, fuel₀ ≤ fuel₂ → ∀ st lv, runLValFuel fuel₀ st lv = o → runLValFuel fuel₂ st lv = o by
    exact this fuel₂ fuel₁ hle st lv h
  intro fuel₂
  induction fuel₂ using Nat.strong_induction_on with
  | _ fuel₂ ih =>
    intro fuel₀ hle st lv h
    cases fuel₂ with
    | zero =>
        cases fuel₀ with
        | zero => exact (hfinal st (Eq.symm (by simpa [runLValFuel_zero_out] using h))).elim
        | succ _ => exact absurd hle (Nat.not_succ_le_zero _)
    | succ fuel' =>
        cases fuel₀ with
        | zero => exact (hfinal st (Eq.symm (by simpa [runLValFuel_zero_out] using h))).elim
        | succ fuel₀' =>
          rw [runLValFuel_step]
          cases hstep : stepLVal st lv with
          | next st' lv' =>
              have hinner : runLValFuel fuel₀' st' lv' = o := by
                simpa [runLValFuel_step, hstep] using h
              have hle' : fuel₀' ≤ fuel' := Nat.le_of_succ_le_succ hle
              exact ih fuel' (Nat.lt_succ_self fuel') fuel₀' hle' st' lv' hinner
          | target _ _ =>
              rw [runLValFuel_step] at h
              rw [hstep] at h
              exact h
          | runtimeError _ _ =>
              rw [runLValFuel_step] at h
              rw [hstep] at h
              exact h

private theorem runArgsFuel_mono {fuel₁ fuel₂ st args o}
    (hle : fuel₁ ≤ fuel₂) (h : runArgsFuel fuel₁ st args = o)
    (hfinal : ∀ st₀, o ≠ .runtimeError st₀ "out of fuel in runArgsFuel") :
    runArgsFuel fuel₂ st args = o := by
  suffices ∀ fuel₂ fuel₀, fuel₀ ≤ fuel₂ → ∀ st args, runArgsFuel fuel₀ st args = o → runArgsFuel fuel₂ st args = o by
    exact this fuel₂ fuel₁ hle st args h
  intro fuel₂
  induction fuel₂ using Nat.strong_induction_on with
  | _ fuel₂ ih =>
    intro fuel₀ hle st args h
    cases fuel₂ with
    | zero =>
        cases fuel₀ with
        | zero => exact (hfinal st (Eq.symm (by simpa [runArgsFuel_zero_out] using h))).elim
        | succ _ => exact absurd hle (Nat.not_succ_le_zero _)
    | succ fuel' =>
        cases fuel₀ with
        | zero => exact (hfinal st (Eq.symm (by simpa [runArgsFuel_zero_out] using h))).elim
        | succ fuel₀' =>
          rw [runArgsFuel_step]
          cases hstep : stepArgs st args with
          | next st' args' =>
              have hinner : runArgsFuel fuel₀' st' args' = o := by
                simpa [runArgsFuel_step, hstep] using h
              have hle' : fuel₀' ≤ fuel' := Nat.le_of_succ_le_succ hle
              exact ih fuel' (Nat.lt_succ_self fuel') fuel₀' hle' st' args' hinner
          | values _ _ =>
              rw [runArgsFuel_step] at h
              rw [hstep] at h
              exact h
          | control _ _ =>
              rw [runArgsFuel_step] at h
              rw [hstep] at h
              exact h
          | runtimeError _ _ =>
              rw [runArgsFuel_step] at h
              rw [hstep] at h
              exact h

mutual

private theorem exprSmallSteps_pos (e : Expr) : 0 < exprSmallSteps e := by
  cases e
  case num v => simp [exprSmallSteps]
  case var v => simp [exprSmallSteps]
  case special v => simp [exprSmallSteps]
  case arrayAccess name idx =>
    have h := exprSmallSteps_pos idx
    simp [exprSmallSteps, h]
  case assign lhs _ rhs =>
    have h1 := lvalSmallSteps_pos lhs
    have h2 := exprSmallSteps_pos rhs
    simp [exprSmallSteps, h1, h2]
  case rel first rest =>
    have h := exprSmallSteps_pos first
    simp [exprSmallSteps, h]
  case bin _ lhs rhs =>
    have h1 := exprSmallSteps_pos lhs
    have h2 := exprSmallSteps_pos rhs
    simp [exprSmallSteps, h1, h2]
  case unary op arg =>
    cases op with
    | neg =>
        have h := exprSmallSteps_pos arg
        simp [exprSmallSteps, h]
    | preIncr =>
        match arg with
        | .var _ | .special _ => simp [exprSmallSteps]
        | .arrayAccess _ idx => have h := exprSmallSteps_pos idx; simp [exprSmallSteps, h]
        | .paren body => have h := exprSmallSteps_pos body; simp [exprSmallSteps, h]
        | .num _ | .assign _ _ _ | .rel _ _ | .bin _ _ _ | .unary _ _ | .call _ _ | .builtin _ _ =>
            simp [exprSmallSteps]
    | preDecr =>
        match arg with
        | .var _ | .special _ => simp [exprSmallSteps]
        | .arrayAccess _ idx => have h := exprSmallSteps_pos idx; simp [exprSmallSteps, h]
        | .paren body => have h := exprSmallSteps_pos body; simp [exprSmallSteps, h]
        | .num _ | .assign _ _ _ | .rel _ _ | .bin _ _ _ | .unary _ _ | .call _ _ | .builtin _ _ =>
            simp [exprSmallSteps]
    | postIncr =>
        match arg with
        | .var _ | .special _ => simp [exprSmallSteps]
        | .arrayAccess _ idx => have h := exprSmallSteps_pos idx; simp [exprSmallSteps, h]
        | .paren body => have h := exprSmallSteps_pos body; simp [exprSmallSteps, h]
        | .num _ | .assign _ _ _ | .rel _ _ | .bin _ _ _ | .unary _ _ | .call _ _ | .builtin _ _ =>
            simp [exprSmallSteps]
    | postDecr =>
        match arg with
        | .var _ | .special _ => simp [exprSmallSteps]
        | .arrayAccess _ idx => have h := exprSmallSteps_pos idx; simp [exprSmallSteps, h]
        | .paren body => have h := exprSmallSteps_pos body; simp [exprSmallSteps, h]
        | .num _ | .assign _ _ _ | .rel _ _ | .bin _ _ _ | .unary _ _ | .call _ _ | .builtin _ _ =>
            simp [exprSmallSteps]
  case call _ args =>
    have h := argsSmallSteps_pos args
    simp [exprSmallSteps, h]
  case builtin _ arg =>
    cases arg with
    | none => simp [exprSmallSteps]
    | some arg =>
        have h := exprSmallSteps_pos arg
        simp [exprSmallSteps, h]
  case paren body =>
    have h := exprSmallSteps_pos body
    simp [exprSmallSteps, h]

private theorem lvalSmallSteps_pos (lv : LVal) : 0 < lvalSmallSteps lv := by
  cases lv
  case var _ => simp [lvalSmallSteps]
  case special _ => simp [lvalSmallSteps]
  case array _ idx =>
    have h := exprSmallSteps_pos idx
    simp [lvalSmallSteps, h]

private theorem argSmallSteps_pos (arg : Arg) : 0 < argSmallSteps arg := by
  cases arg
  case expr e =>
    have h := exprSmallSteps_pos e
    simp [argSmallSteps, h]
  case arrayRef _ => simp [argSmallSteps]

private theorem argsSmallSteps_pos (args : List Arg) : 0 < argsSmallSteps args := by
  cases args with
  | nil => simp [argsSmallSteps]
  | cons arg rest =>
    have h1 := argSmallSteps_pos arg
    have h2 := argsSmallSteps_pos rest
    simp [argsSmallSteps]
    omega

end

private theorem runExprWitness_pos (e : Expr) {fuel : Nat} (hfuel : 0 < fuel) :
    0 < runExprWitness e fuel := by
  have hsteps := exprSmallSteps_pos e
  unfold runExprWitness
  omega

private theorem runLValWitness_pos (lv : LVal) {fuel : Nat} (hfuel : 0 < fuel) :
    0 < runLValWitness lv fuel := by
  have hsteps := lvalSmallSteps_pos lv
  unfold runLValWitness
  omega

private theorem runArgsWitness_pos (args : List Arg) {fuel : Nat} (hfuel : 0 < fuel) :
    0 < runArgsWitness args fuel := by
  have hsteps := argsSmallSteps_pos args
  unfold runArgsWitness
  omega

/-! ### `ofExpr` / `stepExpr` alignment -/

private theorem runExprFuel_value_done {fuel st n} (hfuel : 0 < fuel) :
    runExprFuel fuel st (.value n) = .value st n := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hfuel) with ⟨fuel', rfl⟩
  simp [runExprFuel_step, stepExpr]

private theorem runExprFuel_after_step {fuel st e st' e' o}
    (hstep : stepExpr st e = .next st' e') (hrest : runExprFuel fuel st' e' = o)
    (hfinal : o ≠ .runtimeError st' "out of fuel in runExprFuel") :
    runExprFuel (fuel + 1) st e = o := by
  simpa [runExprFuel_step, hstep] using hrest

private theorem runLValFuel_target_done {fuel st t} (hfuel : 0 < fuel) :
    runLValFuel fuel st (.target t) = .target st t := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hfuel) with ⟨fuel', rfl⟩
  simp [runLValFuel_step, stepLVal]

private theorem runArgsFuel_values_done {fuel st} (hfuel : 0 < fuel) :
    runArgsFuel fuel st [] = .values st [] := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hfuel) with ⟨fuel', rfl⟩
  simp [runArgsFuel_step, stepArgs]

private theorem runLValFuel_after_step {fuel st lv st' lv' o}
    (hstep : stepLVal st lv = .next st' lv') (hrest : runLValFuel fuel st' lv' = o)
    (hfinal : o ≠ .runtimeError st' "out of fuel in runLValFuel") :
    runLValFuel (fuel + 1) st lv = o := by
  simpa [runLValFuel_step, hstep] using hrest

private theorem runArgsFuel_after_step {fuel st args st' args' o}
    (hstep : stepArgs st args = .next st' args') (hrest : runArgsFuel fuel st' args' = o)
    (hfinal : o ≠ .runtimeError st' "out of fuel in runArgsFuel") :
    runArgsFuel (fuel + 1) st args = o := by
  simpa [runArgsFuel_step, hstep] using hrest

private theorem runWitness_succ_le (steps fuel : Nat) :
    fuel * (steps + 1) + steps ≤ (fuel + 1) * (steps + 1) + steps := by
  let m := steps + 1
  let s := steps
  show fuel * m + s ≤ (fuel + 1) * m + s
  calc fuel * m + s ≤ fuel * m + s + m := Nat.le_add_right _ _
    _ = fuel * m + (m + s) := by rw [Nat.add_assoc, Nat.add_comm s m]
    _ = fuel * m + m + s := by rw [← Nat.add_assoc]
    _ = (fuel + 1) * m + s := by rw [← Nat.succ_mul, show fuel + 1 = Nat.succ fuel from rfl]

private theorem runLValWitness_succ_le (lv : LVal) (fuel : Nat) :
    runLValWitness lv fuel ≤ runLValWitness lv (fuel + 1) := by
  unfold runLValWitness
  exact runWitness_succ_le (lvalSmallSteps lv) fuel

private theorem runArgsWitness_succ_le (args : List Arg) (fuel : Nat) :
    runArgsWitness args fuel ≤ runArgsWitness args (fuel + 1) := by
  unfold runArgsWitness
  exact runWitness_succ_le (argsSmallSteps args) fuel

private theorem runExprWitness_succ_le (e : Expr) (fuel : Nat) :
    runExprWitness e fuel ≤ runExprWitness e (fuel + 1) := by
  unfold runExprWitness
  exact runWitness_succ_le (exprSmallSteps e) fuel

private theorem runExprWitness_relRest_le {rest : List (RelOp × Expr)} {fuel : Nat} :
    runExprWitness (.rel (Expr.num "0") rest) fuel ≤
      runExprWitness (.rel (Expr.num "0") rest) (fuel + 1) := by
  exact runExprWitness_succ_le (.rel (Expr.num "0") rest) fuel

private theorem relRestSmallSteps_pos (rest : List (RelOp × Expr)) :
    0 < relRestSmallSteps rest + 2 := by
  simp [relRestSmallSteps]

private theorem evalLValueTarget_to_runLValFuel_zero {st lv r}
    (h : evalLValueTarget 0 st lv = r) (hne : r ≠ .outOfFuel st) : False := by
  simp [evalLValueTarget] at h
  exact hne h.symm

private theorem evalArgValues_to_runArgsFuel_zero {st args r}
    (h : evalArgValues 0 st args = r) (hne : r ≠ .outOfFuel st) : False := by
  simp [evalArgValues] at h
  exact hne h.symm

private theorem evalRelChain_to_runExprFuel_zero {st left rest r}
    (h : evalRelChain 0 st left rest = r) (hne : r ≠ .outOfFuel st) : False := by
  simp [evalRelChain] at h
  exact hne h.symm

private theorem evalExpr_to_runExprFuel_zero {st e r}
    (h : evalExpr 0 st e = r) (hne : r ≠ .outOfFuel st) : False := by
  simp [evalExpr] at h
  exact hne h.symm

private theorem runExprFuel_lit2_done {fuel st} (term : ExprTerm) (n : Num)
    (hstep : stepExpr st term = .next st (.value n)) (hfuel : 2 ≤ fuel) :
    runExprFuel fuel st term = .value st n := by
  have hpos : 0 < fuel := Nat.lt_of_lt_of_le Nat.zero_lt_one
    (Nat.le_trans (by decide : 1 ≤ 2) hfuel)
  obtain ⟨fuel', heq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  subst heq
  rw [runExprFuel_step, hstep]
  cases fuel' with
  | zero =>
      have : False := by omega
      exact False.elim this
  | succ fuel'' => exact runExprFuel_value_done (Nat.succ_pos fuel'')

private theorem runExprFuel_num_done {fuel st raw} (hfuel : 2 ≤ fuel) :
    runExprFuel fuel st (.num raw) =
      .value st (Num.ofInputString raw (currentConstBase st)) := by
  have hstep : stepExpr st (.num raw) =
      .next st (.value (Num.ofInputString raw (currentConstBase st))) := rfl
  exact runExprFuel_lit2_done (.num raw) _ hstep hfuel

private theorem runExprFuel_var_done {fuel st name} (hfuel : 2 ≤ fuel) :
    runExprFuel fuel st (.var name) = .value st (lookupScalar st name) := by
  have hstep : stepExpr st (.var name) = .next st (.value (lookupScalar st name)) := rfl
  exact runExprFuel_lit2_done (.var name) _ hstep hfuel

private theorem runExprFuel_special_done {fuel st v} (hfuel : 2 ≤ fuel) :
    runExprFuel fuel st (.special v) = .value st (specialValue st v) := by
  have hstep : stepExpr st (.special v) = .next st (.value (specialValue st v)) := rfl
  exact runExprFuel_lit2_done (.special v) _ hstep hfuel

private theorem runExprWitness_ge_two (e : Expr) {fuel : Nat} (hfuel : 0 < fuel) :
    2 ≤ runExprWitness e fuel := by
  have hsteps1 : 1 ≤ exprSmallSteps e := Nat.succ_le_iff.mp (exprSmallSteps_pos e)
  have hfuel1 : 1 ≤ fuel := Nat.succ_le_iff.mpr hfuel
  unfold runExprWitness
  have hbase : 2 ≤ 1 * (exprSmallSteps e + 1) + exprSmallSteps e := by
    simp [Nat.one_mul, Nat.add_assoc]
    omega
  have hle : 1 * (exprSmallSteps e + 1) + exprSmallSteps e ≤
      fuel * (exprSmallSteps e + 1) + exprSmallSteps e := by
    dsimp
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hfuel1) _
  exact Nat.le_trans hbase hle

end BigSmall

end Bc
