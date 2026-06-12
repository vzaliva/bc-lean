/-
  Anti-evaluation: one executable small step preserves residual big-step
  evaluation.

  For every layer X: if `stepX st t` produces outcome `o`, and the continuation
  of `o` evaluates (via the residual interpreter) to a final result `r`, then
  `t` itself evaluates to `r` with some fuel.  Together with the finite-run
  closures (`Bc/BigSmall/Run.lean`) this yields the backward simulation:
  a finite small-step run is reproduced by the residual interpreter.
-/

import Bc.BigSmall.BackwardSim
import Bc.BigSmall.Forward

namespace Bc

namespace BigSmall

open SmallStep

set_option maxHeartbeats 1600000

/-! ### Outcome continuations -/

/-- Evaluate the continuation of an expression step outcome. -/
def exprCont (fb : Nat) : ExprOutcome → EvalResult Num
  | .next st e => evalExprTerm fb st e
  | .value st v => .ok st v
  | .control st c => .control st c
  | .runtimeError st msg => .runtimeError st msg

/-- Evaluate the continuation of an lvalue step outcome. -/
def lvalCont (fb : Nat) : LValOutcome → EvalResult LValueTarget
  | .next st lv => evalLValTerm fb st lv
  | .target st t => .ok st t
  | .runtimeError st msg => .runtimeError st msg

/-- Evaluate the continuation of an argument-list step outcome. -/
def argsCont (fb : Nat) : ArgListOutcome → EvalResult (List (Sum Num Name))
  | .next st as => evalArgTerms fb st as
  | .values st vs => .ok st vs
  | .control st c => .control st c
  | .runtimeError st msg => .runtimeError st msg

/-- Evaluate the continuation of a statement step outcome. -/
def stmtCont (fb : Nat) : StmtOutcome → Result Control
  | .next st s => evalStmtTerm fb st s
  | .done st => .ok st .normal
  | .control st c => .ok st c
  | .runtimeError st msg => .runtimeError st msg

/-- Evaluate the continuation of a body step outcome. -/
def bodyCont (fb : Nat) : BodyOutcome → Result Control
  | .next st b => evalBodyTerm fb st b
  | .done st => .ok st .normal
  | .control st c => .ok st c
  | .runtimeError st msg => .runtimeError st msg

/-! ### Helpers -/

theorem notFuelE {α : Type} {st : RuntimeState} {r : EvalResult α} {C : Prop}
    (h : EvalResult.outOfFuel st = r) (hnf : EvalResultNotFuel r) : C := by
  subst h
  exact absurd hnf (by simp [EvalResultNotFuel])

theorem notFuelR {st : RuntimeState} {r : Result Control} {C : Prop}
    (h : Result.outOfFuel st = r) (hnf : ResultNotFuel r) : C := by
  subst h
  exact absurd hnf (by simp [ResultNotFuel])

private theorem monoE {n N st e v} (hle : n ≤ N) (hsub : evalExprTerm n st e = v)
    (hv : EvalResultNotFuel v) : evalExprTerm N st e = v :=
  evalExprTerm_mono hle hsub hv

/-- Brute-force head unfolding of the residual interpreter on literal-fuel
applications, interleaved with iota normalization. Symbolic-fuel applications
are left for monotonicity facts. -/
local macro "unfold_eval" : tactic =>
  `(tactic| repeat' (first
      | rw [evalExprTerm]
      | rw [evalLValTerm]
      | rw [evalRelChainTerm]
      | rw [evalArgTerms]
      | rw [evalStmtTerm]
      | rw [evalBodyTerm]
      | simp only []))

/-! ### Anti-evaluation, mutual over the five layers -/

mutual

theorem antiExpr : (e : ExprTerm) → ∀ {st fb r},
    exprCont fb (stepExpr st e) = r → EvalResultNotFuel r →
    ∃ fb2, evalExprTerm fb2 st e = r
  | .value n => by
      rename_i st fb r; intro h hnf
      simp only [stepExpr, exprCont] at h
      exact ⟨1, h⟩
  | .num raw => by
      rename_i st fb r; intro h hnf
      simp only [stepExpr, exprCont] at h
      cases fb with
      | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
      | succ fb' => simp only [evalExprTerm] at h; exact ⟨1, h⟩
  | .var name => by
      rename_i st fb r; intro h hnf
      simp only [stepExpr, exprCont] at h
      cases fb with
      | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
      | succ fb' => simp only [evalExprTerm] at h; exact ⟨1, h⟩
  | .special v => by
      rename_i st fb r; intro h hnf
      simp only [stepExpr, exprCont] at h
      cases fb with
      | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
      | succ fb' => simp only [evalExprTerm] at h; exact ⟨1, h⟩
  | .arrayAccess name index => by
      rename_i st fb r; intro h hnf
      cases hsub : stepExpr st index with
      | value st₁ v =>
          obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub
          simp only [stepExpr] at h
          cases hidx : indexOfNum? v with
          | ok idx =>
              cases hens : ensureArrayId st name with
              | mk st₂ id =>
                  simp only [hidx, hens, exprCont] at h
                  cases fb with
                  | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
                  | succ fb' =>
                      simp only [evalExprTerm] at h
                      exact ⟨2, by unfold_eval; simp only [hidx, hens]; exact h⟩
          | error msg =>
              simp only [hidx, exprCont] at h
              exact ⟨2, by unfold_eval; simp only [hidx]; exact h⟩
      | next st₁ index' =>
          rw [stepExpr_arrayAccess_next (name := name) hsub] at h
          simp only [exprCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
          | succ fb' =>
              simp only [evalExprTerm] at h
              cases hsub2 : evalExprTerm fb' st₁ index' <;>
                first
                | (simp only [hsub2] at h; exact notFuelE h hnf)
                | (obtain ⟨f₁, hf₁⟩ := antiExpr index (st := st) (fb := fb')
                     (by simpa [hsub, exprCont] using hsub2)
                     (by simp [EvalResultNotFuel])
                   simp only [hsub2] at h
                   exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩)
      | control st₁ c =>
          rw [stepExpr_arrayAccess_control (name := name) hsub] at h
          simp only [exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr index (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepExpr_arrayAccess_error (name := name) hsub] at h
          simp only [exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr index (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
  | .assign lhs op rhs => by
      rename_i st fb r; intro h hnf
      cases hsub : stepLVal st lhs with
      | target st₁ t =>
          obtain ⟨rfl, -⟩ := stepLVal_target_inv hsub
          simp only [stepExpr, exprCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
          | succ fb' =>
              simp only [evalExprTerm] at h
              cases hsub2 : evalExprTerm fb' st rhs with
              | outOfFuel stx => simp only [hsub2] at h; exact notFuelE h hnf
              | ok st₂ v =>
                  simp only [hsub2] at h
                  refine ⟨fb' + 2, ?_⟩
                  rw [evalExprTerm]
                  try simp only []
                  rw [evalLValTerm]
                  simp only [monoE (Nat.le_succ fb') hsub2 (by simp [EvalResultNotFuel])]
                  exact h
              | control st₂ c =>
                  simp only [hsub2] at h
                  refine ⟨fb' + 2, ?_⟩
                  rw [evalExprTerm]
                  try simp only []
                  rw [evalLValTerm]
                  simp only [monoE (Nat.le_succ fb') hsub2 (by simp [EvalResultNotFuel])]
                  exact h
              | runtimeError st₂ msg =>
                  simp only [hsub2] at h
                  refine ⟨fb' + 2, ?_⟩
                  rw [evalExprTerm]
                  try simp only []
                  rw [evalLValTerm]
                  simp only [monoE (Nat.le_succ fb') hsub2 (by simp [EvalResultNotFuel])]
                  exact h
      | next st₁ lhs' =>
          rw [stepExpr_assign_lval_next hsub] at h
          simp only [exprCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
          | succ fb' =>
              simp only [evalExprTerm] at h
              cases hsub2 : evalLValTerm fb' st₁ lhs' with
              | outOfFuel stx => simp only [hsub2] at h; exact notFuelE h hnf
              | control stx c => exact absurd hsub2 evalLValTerm_no_control
              | ok st₂ t =>
                  obtain ⟨f₁, hf₁⟩ := antiLVal lhs (st := st) (fb := fb')
                    (by simpa [hsub, lvalCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  cases hsub3 : evalExprTerm fb' st₂ rhs <;>
                    first
                    | (simp only [hsub3] at h; exact notFuelE h hnf)
                    | (simp only [hsub3] at h
                       refine ⟨max f₁ fb' + 1, ?_⟩
                       rw [evalExprTerm]
                       simp only [evalLValTerm_mono (show f₁ ≤ max f₁ fb' by omega) hf₁ (by simp [EvalResultNotFuel]), monoE (show fb' ≤ max f₁ fb' by omega) hsub3 (by simp [EvalResultNotFuel])]
                       exact h)
              | runtimeError st₂ msg =>
                  obtain ⟨f₁, hf₁⟩ := antiLVal lhs (st := st) (fb := fb')
                    (by simpa [hsub, lvalCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepExpr_assign_lval_error hsub] at h
          simp only [exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiLVal lhs (st := st) (fb := fb)
            (by rw [hsub]) (by simp [lvalCont, EvalResultNotFuel])
          simp only [lvalCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
  | .assignTarget t op rhs => by
      rename_i st fb r; intro h hnf
      cases hsub : stepExpr st rhs with
      | value st₁ v =>
          obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub
          simp only [stepExpr] at h
          cases happ : applyAssign? op (readLValueTarget st t) v st.scale with
          | ok result =>
              simp only [happ, exprCont] at h
              cases fb with
              | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
              | succ fb' =>
                  simp only [evalExprTerm] at h
                  exact ⟨2, by unfold_eval; simp only [happ]; exact h⟩
          | error msg =>
              simp only [happ, exprCont] at h
              exact ⟨2, by unfold_eval; simp only [happ]; exact h⟩
      | next st₁ rhs' =>
          rw [stepExpr_assignTarget_rhs_next hsub] at h
          simp only [exprCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
          | succ fb' =>
              simp only [evalExprTerm] at h
              cases hsub2 : evalExprTerm fb' st₁ rhs' <;>
                first
                | (simp only [hsub2] at h; exact notFuelE h hnf)
                | (obtain ⟨f₁, hf₁⟩ := antiExpr rhs (st := st) (fb := fb')
                     (by simpa [hsub, exprCont] using hsub2)
                     (by simp [EvalResultNotFuel])
                   simp only [hsub2] at h
                   exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩)
      | control st₁ c =>
          rw [stepExpr_assignTarget_rhs_control hsub] at h
          simp only [exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr rhs (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepExpr_assignTarget_rhs_error hsub] at h
          simp only [exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr rhs (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
  | .rel first rest => by
      rename_i st fb r; intro h hnf
      cases hsub : stepExpr st first with
      | value st₁ left =>
          obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub
          cases rest with
          | nil =>
              simp only [stepExpr, exprCont] at h
              cases fb with
              | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
              | succ fb' =>
                  simp only [evalExprTerm] at h
                  exact ⟨2, by rw [evalExprTerm]; simp only [evalRelChainTerm]; exact h⟩
          | cons hd tail =>
              obtain ⟨op, rhs⟩ := hd
              cases hsub2 : stepExpr st rhs with
              | value st₁ right =>
                  obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub2
                  cases tail with
                  | nil =>
                      simp only [stepExpr, exprCont] at h
                      cases fb with
                      | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
                      | succ fb' =>
                          simp only [evalExprTerm] at h
                          exact ⟨3, by rw [evalExprTerm]; simp only [evalRelChainTerm]; exact h⟩
                  | cons p t2 =>
                      simp only [stepExpr, exprCont] at h
                      cases fb with
                      | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
                      | succ fb' =>
                          simp only [evalExprTerm] at h
                          cases fb' with
                          | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
                          | succ k =>
                              simp only [evalExprTerm] at h
                              refine ⟨k + 4, ?_⟩
                              rw [evalExprTerm]
                              rw [evalExprTerm]
                              try simp only []
                              rw [evalRelChainTerm]
                              rw [evalExprTerm]
                              simp only [evalRelChainTerm_mono (show k + 1 ≤ k + 2 by omega) h hnf]
              | next st₁ rhs' =>
                  rw [stepExpr_rel_rhs_next hsub2] at h
                  simp only [exprCont] at h
                  cases fb with
                  | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
                  | succ fb' =>
                      simp only [evalExprTerm] at h
                      cases fb' with
                      | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
                      | succ k =>
                          simp only [evalExprTerm, evalRelChainTerm] at h
                          cases hsub3 : evalExprTerm k st₁ rhs' with
                          | outOfFuel stx => simp only [hsub3] at h; exact notFuelE h hnf
                          | ok st₂ right =>
                              obtain ⟨f₁, hf₁⟩ := antiExpr rhs (st := st) (fb := k)
                                (by simpa [hsub2, exprCont] using hsub3)
                                (by simp [EvalResultNotFuel])
                              simp only [hsub3] at h
                              cases tail with
                              | nil =>
                                  refine ⟨max f₁ k + 3, ?_⟩
                                  rw [evalExprTerm]
                                  try simp only []
                                  rw [evalExprTerm]
                                  try simp only []
                                  rw [evalRelChainTerm]
                                  simp only [monoE (show f₁ ≤ max f₁ k + 1 by omega) hf₁ (by simp [EvalResultNotFuel])]
                                  exact h
                              | cons p t2 =>
                                  cases hsub4 : evalRelChainTerm k st₂
                                      (boolNum (applyRel op left right)) (p :: t2) with
                                  | outOfFuel stx =>
                                      simp only [hsub4] at h; exact notFuelE h hnf
                                  | ok stx vx =>
                                      simp only [hsub4] at h
                                      refine ⟨max f₁ k + 3, ?_⟩
                                      rw [evalExprTerm]
                                      try simp only []
                                      rw [evalExprTerm]
                                      try simp only []
                                      rw [evalRelChainTerm]
                                      simp only [monoE (show f₁ ≤ max f₁ k + 1 by omega) hf₁ (by simp [EvalResultNotFuel]),
                                        evalRelChainTerm_mono (show k ≤ max f₁ k + 1 by omega) hsub4 (by simp [EvalResultNotFuel])]
                                      exact h
                                  | control stx c =>
                                      simp only [hsub4] at h
                                      refine ⟨max f₁ k + 3, ?_⟩
                                      rw [evalExprTerm]
                                      try simp only []
                                      rw [evalExprTerm]
                                      try simp only []
                                      rw [evalRelChainTerm]
                                      simp only [monoE (show f₁ ≤ max f₁ k + 1 by omega) hf₁ (by simp [EvalResultNotFuel]),
                                        evalRelChainTerm_mono (show k ≤ max f₁ k + 1 by omega) hsub4 (by simp [EvalResultNotFuel])]
                                      exact h
                                  | runtimeError stx msg =>
                                      simp only [hsub4] at h
                                      refine ⟨max f₁ k + 3, ?_⟩
                                      rw [evalExprTerm]
                                      try simp only []
                                      rw [evalExprTerm]
                                      try simp only []
                                      rw [evalRelChainTerm]
                                      simp only [monoE (show f₁ ≤ max f₁ k + 1 by omega) hf₁ (by simp [EvalResultNotFuel]),
                                        evalRelChainTerm_mono (show k ≤ max f₁ k + 1 by omega) hsub4 (by simp [EvalResultNotFuel])]
                                      exact h
                          | control st₂ c =>
                              obtain ⟨f₁, hf₁⟩ := antiExpr rhs (st := st) (fb := k)
                                (by simpa [hsub2, exprCont] using hsub3)
                                (by simp [EvalResultNotFuel])
                              simp only [hsub3] at h
                              refine ⟨f₁ + 3, ?_⟩
                              rw [evalExprTerm]
                              try simp only []
                              rw [evalExprTerm]
                              try simp only []
                              rw [evalRelChainTerm]
                              simp only [monoE (show f₁ ≤ f₁ + 1 by omega) hf₁ (by simp [EvalResultNotFuel])]
                              exact h
                          | runtimeError st₂ msg =>
                              obtain ⟨f₁, hf₁⟩ := antiExpr rhs (st := st) (fb := k)
                                (by simpa [hsub2, exprCont] using hsub3)
                                (by simp [EvalResultNotFuel])
                              simp only [hsub3] at h
                              refine ⟨f₁ + 3, ?_⟩
                              rw [evalExprTerm]
                              try simp only []
                              rw [evalExprTerm]
                              try simp only []
                              rw [evalRelChainTerm]
                              simp only [monoE (show f₁ ≤ f₁ + 1 by omega) hf₁ (by simp [EvalResultNotFuel])]
                              exact h
              | control st₁ c =>
                  rw [stepExpr_rel_rhs_control hsub2] at h
                  simp only [exprCont] at h
                  obtain ⟨f₁, hf₁⟩ := antiExpr rhs (st := st) (fb := fb)
                    (by rw [hsub2]) (by simp [exprCont, EvalResultNotFuel])
                  simp only [exprCont] at hf₁
                  refine ⟨f₁ + 3, ?_⟩
                  rw [evalExprTerm]
                  try simp only []
                  rw [evalExprTerm]
                  try simp only []
                  rw [evalRelChainTerm]
                  simp only [monoE (show f₁ ≤ f₁ + 1 by omega) hf₁ (by simp [EvalResultNotFuel])]
                  exact h
              | runtimeError st₁ msg =>
                  rw [stepExpr_rel_rhs_error hsub2] at h
                  simp only [exprCont] at h
                  obtain ⟨f₁, hf₁⟩ := antiExpr rhs (st := st) (fb := fb)
                    (by rw [hsub2]) (by simp [exprCont, EvalResultNotFuel])
                  simp only [exprCont] at hf₁
                  refine ⟨f₁ + 3, ?_⟩
                  rw [evalExprTerm]
                  try simp only []
                  rw [evalExprTerm]
                  try simp only []
                  rw [evalRelChainTerm]
                  simp only [monoE (show f₁ ≤ f₁ + 1 by omega) hf₁ (by simp [EvalResultNotFuel])]
                  exact h
      | next st₁ first' =>
          rw [stepExpr_rel_first_next hsub] at h
          simp only [exprCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
          | succ fb' =>
              simp only [evalExprTerm] at h
              cases hsub2 : evalExprTerm fb' st₁ first' with
              | outOfFuel stx => simp only [hsub2] at h; exact notFuelE h hnf
              | ok st₂ left =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr first (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  cases hsub3 : evalRelChainTerm fb' st₂ left rest with
                  | outOfFuel stx => simp only [hsub3] at h; exact notFuelE h hnf
                  | ok stx vx =>
                      simp only [hsub3] at h
                      refine ⟨max f₁ fb' + 1, ?_⟩
                      rw [evalExprTerm]
                      simp only [monoE (show f₁ ≤ max f₁ fb' by omega) hf₁ (by simp [EvalResultNotFuel]), evalRelChainTerm_mono (show fb' ≤ max f₁ fb' by omega) hsub3 (by simp [EvalResultNotFuel])]
                      exact h
                  | control stx c =>
                      simp only [hsub3] at h
                      refine ⟨max f₁ fb' + 1, ?_⟩
                      rw [evalExprTerm]
                      simp only [monoE (show f₁ ≤ max f₁ fb' by omega) hf₁ (by simp [EvalResultNotFuel]), evalRelChainTerm_mono (show fb' ≤ max f₁ fb' by omega) hsub3 (by simp [EvalResultNotFuel])]
                      exact h
                  | runtimeError stx msg =>
                      simp only [hsub3] at h
                      refine ⟨max f₁ fb' + 1, ?_⟩
                      rw [evalExprTerm]
                      simp only [monoE (show f₁ ≤ max f₁ fb' by omega) hf₁ (by simp [EvalResultNotFuel]), evalRelChainTerm_mono (show fb' ≤ max f₁ fb' by omega) hsub3 (by simp [EvalResultNotFuel])]
                      exact h
              | control st₂ c =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr first (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
              | runtimeError st₂ msg =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr first (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
      | control st₁ c =>
          rw [stepExpr_rel_first_control hsub] at h
          simp only [exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr first (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepExpr_rel_first_error hsub] at h
          simp only [exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr first (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
  | .bin op lhs rhs => by
      rename_i st fb r; intro h hnf
      cases hsub : stepExpr st lhs with
      | value st₁ left =>
          obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub
          cases hsub2 : stepExpr st rhs with
          | value st₁ right =>
              obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub2
              simp only [stepExpr] at h
              cases happ : applyBin? op left right st.scale with
              | ok result =>
                  simp only [happ, exprCont] at h
                  cases fb with
                  | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
                  | succ fb' =>
                      simp only [evalExprTerm] at h
                      exact ⟨2, by unfold_eval; simp only [happ]; exact h⟩
              | error msg =>
                  simp only [happ, exprCont] at h
                  exact ⟨2, by unfold_eval; simp only [happ]; exact h⟩
          | next st₁ rhs' =>
              rw [stepExpr_bin_rhs_next hsub2] at h
              simp only [exprCont] at h
              cases fb with
              | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
              | succ fb' =>
                  rw [evalExprTerm] at h
                  cases fb' with
                  | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
                  | succ k =>
                      rw [evalExprTerm] at h
                      simp only [] at h
                      cases hsub3 : evalExprTerm (k + 1) st₁ rhs' <;>
                        first
                        | (simp only [hsub3] at h; exact notFuelE h hnf)
                        | (obtain ⟨f₁, hf₁⟩ := antiExpr rhs (st := st) (fb := k + 1)
                             (by simpa [hsub2, exprCont] using hsub3)
                             (by simp [EvalResultNotFuel])
                           simp only [hsub3] at h
                           refine ⟨f₁ + 2, ?_⟩
                           unfold_eval
                           simp only [monoE (show f₁ ≤ f₁ + 1 by omega) hf₁ (by simp [EvalResultNotFuel])]
                           exact h)
          | control st₁ c =>
              rw [stepExpr_bin_rhs_control hsub2] at h
              simp only [exprCont] at h
              obtain ⟨f₁, hf₁⟩ := antiExpr rhs (st := st) (fb := fb)
                (by rw [hsub2]) (by simp [exprCont, EvalResultNotFuel])
              simp only [exprCont] at hf₁
              refine ⟨f₁ + 2, ?_⟩
              rw [evalExprTerm]
              try simp only []
              rw [evalExprTerm]
              simp only [monoE (show f₁ ≤ f₁ + 1 by omega) hf₁ (by simp [EvalResultNotFuel])]
              exact h
          | runtimeError st₁ msg =>
              rw [stepExpr_bin_rhs_error hsub2] at h
              simp only [exprCont] at h
              obtain ⟨f₁, hf₁⟩ := antiExpr rhs (st := st) (fb := fb)
                (by rw [hsub2]) (by simp [exprCont, EvalResultNotFuel])
              simp only [exprCont] at hf₁
              refine ⟨f₁ + 2, ?_⟩
              rw [evalExprTerm]
              try simp only []
              rw [evalExprTerm]
              simp only [monoE (show f₁ ≤ f₁ + 1 by omega) hf₁ (by simp [EvalResultNotFuel])]
              exact h
      | next st₁ lhs' =>
          rw [stepExpr_bin_lhs_next hsub] at h
          simp only [exprCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
          | succ fb' =>
              simp only [evalExprTerm] at h
              cases hsub2 : evalExprTerm fb' st₁ lhs' with
              | outOfFuel stx => simp only [hsub2] at h; exact notFuelE h hnf
              | ok st₂ left =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr lhs (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  cases hsub3 : evalExprTerm fb' st₂ rhs <;>
                    first
                    | (simp only [hsub3] at h; exact notFuelE h hnf)
                    | (simp only [hsub3] at h
                       refine ⟨max f₁ fb' + 1, ?_⟩
                       rw [evalExprTerm]
                       simp only [monoE (show f₁ ≤ max f₁ fb' by omega) hf₁ (by simp [EvalResultNotFuel]), monoE (show fb' ≤ max f₁ fb' by omega) hsub3 (by simp [EvalResultNotFuel])]
                       exact h)
              | control st₂ c =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr lhs (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
              | runtimeError st₂ msg =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr lhs (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
      | control st₁ c =>
          rw [stepExpr_bin_lhs_control hsub] at h
          simp only [exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr lhs (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepExpr_bin_lhs_error hsub] at h
          simp only [exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr lhs (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
  | .neg arg => by
      rename_i st fb r; intro h hnf
      cases hsub : stepExpr st arg with
      | value st₁ v =>
          obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub
          simp only [stepExpr, exprCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
          | succ fb' =>
              simp only [evalExprTerm] at h
              exact ⟨2, by unfold_eval; exact h⟩
      | next st₁ arg' =>
          rw [stepExpr_neg_next hsub] at h
          simp only [exprCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
          | succ fb' =>
              simp only [evalExprTerm] at h
              cases hsub2 : evalExprTerm fb' st₁ arg' <;>
                first
                | (simp only [hsub2] at h; exact notFuelE h hnf)
                | (obtain ⟨f₁, hf₁⟩ := antiExpr arg (st := st) (fb := fb')
                     (by simpa [hsub, exprCont] using hsub2)
                     (by simp [EvalResultNotFuel])
                   simp only [hsub2] at h
                   exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩)
      | control st₁ c =>
          rw [stepExpr_neg_control hsub] at h
          simp only [exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr arg (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepExpr_neg_error hsub] at h
          simp only [exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr arg (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
  | .bump op target => by
      rename_i st fb r; intro h hnf
      cases hsub : stepLVal st target with
      | target st₁ t =>
          obtain ⟨rfl, -⟩ := stepLVal_target_inv hsub
          simp only [stepExpr, exprCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
          | succ fb' =>
              simp only [evalExprTerm] at h
              exact ⟨2, by unfold_eval; cases op <;> exact h⟩
      | next st₁ target' =>
          rw [stepExpr_bump_lval_next hsub] at h
          simp only [exprCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
          | succ fb' =>
              simp only [evalExprTerm] at h
              cases hsub2 : evalLValTerm fb' st₁ target' with
              | outOfFuel stx => simp only [hsub2] at h; exact notFuelE h hnf
              | control stx c => exact absurd hsub2 evalLValTerm_no_control
              | ok st₂ t =>
                  obtain ⟨f₁, hf₁⟩ := antiLVal target (st := st) (fb := fb')
                    (by simpa [hsub, lvalCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
              | runtimeError st₂ msg =>
                  obtain ⟨f₁, hf₁⟩ := antiLVal target (st := st) (fb := fb')
                    (by simpa [hsub, lvalCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepExpr_bump_lval_error hsub] at h
          simp only [exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiLVal target (st := st) (fb := fb)
            (by rw [hsub]) (by simp [lvalCont, EvalResultNotFuel])
          simp only [lvalCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
  | .badBump op arg => by
      rename_i st fb r; intro h hnf
      simp only [stepExpr, exprCont] at h
      exact ⟨1, h⟩
  | .call name args => by
      rename_i st fb r; intro h hnf
      simp only [stepExpr] at h
      cases hlk : lookupFunction st name with
      | none =>
          simp only [hlk, exprCont] at h
          exact ⟨1, by rw [evalExprTerm]; simp only [hlk]; exact h⟩
      | some defn =>
          simp only [hlk] at h
          cases hargs : stepArgs st args with
          | next st₁ args' =>
              simp only [hargs, exprCont] at h
              cases fb with
              | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
              | succ fb' =>
                  have hlk1 : lookupFunction st₁ name = some defn :=
                    (stepArgs_next_lookupFunction name hargs).trans hlk
                  simp only [evalExprTerm, hlk1] at h
                  cases hsub2 : evalArgTerms fb' st₁ args' with
                  | outOfFuel stx => simp only [hsub2] at h; exact notFuelE h hnf
                  | ok stA av =>
                      obtain ⟨f₁, hf₁⟩ := antiArgs args (st := st) (fb := fb')
                        (by simpa [hargs, argsCont] using hsub2)
                        (by simp [EvalResultNotFuel])
                      simp only [hsub2] at h
                      cases hbind : bindParams
                          { stA with frames := { constBase := stA.ibase } :: stA.frames }
                          defn.params av with
                      | error msg =>
                          simp only [hbind] at h
                          refine ⟨max f₁ fb' + 1, ?_⟩
                          simp only [evalExprTerm, hlk,
                            evalArgTerms_mono (show f₁ ≤ max f₁ fb' by omega) hf₁
                              (by simp [EvalResultNotFuel]), hbind]
                          exact h
                      | ok stB =>
                          simp only [hbind] at h
                          refine ⟨max f₁ fb' + 1, ?_⟩
                          simp only [evalExprTerm, hlk,
                            evalArgTerms_mono (show f₁ ≤ max f₁ fb' by omega) hf₁
                              (by simp [EvalResultNotFuel]), hbind]
                          exact monoE (by omega) h hnf
                  | control stA c =>
                      obtain ⟨f₁, hf₁⟩ := antiArgs args (st := st) (fb := fb')
                        (by simpa [hargs, argsCont] using hsub2)
                        (by simp [EvalResultNotFuel])
                      simp only [hsub2] at h
                      exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hlk, hf₁]; exact h⟩
                  | runtimeError stA msg =>
                      obtain ⟨f₁, hf₁⟩ := antiArgs args (st := st) (fb := fb')
                        (by simpa [hargs, argsCont] using hsub2)
                        (by simp [EvalResultNotFuel])
                      simp only [hsub2] at h
                      exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hlk, hf₁]; exact h⟩
          | values st₁ argValues =>
              simp only [hargs] at h
              obtain ⟨f₁, hf₁⟩ := antiArgs args (st := st) (fb := fb)
                (by rw [hargs]) (by simp [argsCont, EvalResultNotFuel])
              simp only [argsCont] at hf₁
              unfold enterFunction at h
              simp only at h
              cases hbind : bindParams
                  { st₁ with frames := { constBase := st₁.ibase } :: st₁.frames }
                  defn.params argValues with
              | error msg =>
                  simp only [hbind, exprCont] at h
                  exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hlk, hf₁, hbind]; exact h⟩
              | ok stB =>
                  simp only [hbind, exprCont] at h
                  refine ⟨max f₁ fb + 1, ?_⟩
                  simp only [evalExprTerm, hlk,
                    evalArgTerms_mono (show f₁ ≤ max f₁ fb by omega) hf₁
                      (by simp [EvalResultNotFuel]), hbind]
                  exact monoE (by omega) h hnf
          | control st₁ c =>
              simp only [hargs, exprCont] at h
              obtain ⟨f₁, hf₁⟩ := antiArgs args (st := st) (fb := fb)
                (by rw [hargs]) (by simp [argsCont, EvalResultNotFuel])
              simp only [argsCont] at hf₁
              exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hlk, hf₁]; exact h⟩
          | runtimeError st₁ msg =>
              simp only [hargs, exprCont] at h
              obtain ⟨f₁, hf₁⟩ := antiArgs args (st := st) (fb := fb)
                (by rw [hargs]) (by simp [argsCont, EvalResultNotFuel])
              simp only [argsCont] at hf₁
              exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hlk, hf₁]; exact h⟩
  | .activeCall body => by
      rename_i st fb r; intro h hnf
      simp only [stepExpr] at h
      cases hsub : stepBody st body with
      | next st₁ body' =>
          simp only [hsub, exprCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
          | succ fb' =>
              simp only [evalExprTerm] at h
              cases hsub2 : evalBodyTerm fb' st₁ body' with
              | outOfFuel stx => simp only [hsub2] at h; exact notFuelE h hnf
              | ok stB c =>
                  obtain ⟨f₁, hf₁⟩ := antiBody body (st := st) (fb := fb')
                    (by simpa [hsub, bodyCont] using hsub2)
                    (by simp [ResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
              | runtimeError stB msg =>
                  obtain ⟨f₁, hf₁⟩ := antiBody body (st := st) (fb := fb')
                    (by simpa [hsub, bodyCont] using hsub2)
                    (by simp [ResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
      | done st₁ =>
          simp only [hsub, exprCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
          | succ fb' =>
              simp only [evalExprTerm] at h
              obtain ⟨f₁, hf₁⟩ := antiBody body (st := st) (fb := 0)
                (by rw [hsub]) (by simp [bodyCont, ResultNotFuel])
              simp only [bodyCont] at hf₁
              exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
      | control st₁ c =>
          obtain ⟨f₁, hf₁⟩ := antiBody body (st := st) (fb := fb)
            (by rw [hsub]) (by simp [bodyCont, ResultNotFuel])
          simp only [bodyCont] at hf₁
          cases c with
          | normal =>
              simp only [hsub, exprCont] at h
              cases fb with
              | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
              | succ fb' =>
                  simp only [evalExprTerm] at h
                  exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
          | «break» =>
              simp only [hsub, exprCont] at h
              exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
          | «return» v? =>
              simp only [hsub, exprCont] at h
              cases fb with
              | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
              | succ fb' =>
                  simp only [evalExprTerm] at h
                  exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
          | quit =>
              simp only [hsub, exprCont] at h
              exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          simp only [hsub, exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiBody body (st := st) (fb := fb)
            (by rw [hsub]) (by simp [bodyCont, ResultNotFuel])
          simp only [bodyCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
  | .builtin fn none => by
      rename_i st fb r; intro h hnf
      simp only [stepExpr, exprCont] at h
      exact ⟨1, h⟩
  | .builtin fn (some arg) => by
      rename_i st fb r; intro h hnf
      cases hsub : stepExpr st arg with
      | value st₁ v =>
          obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub
          simp only [stepExpr] at h
          cases happ : applyBuiltin? fn v st.scale with
          | ok result =>
              simp only [happ, exprCont] at h
              cases fb with
              | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
              | succ fb' =>
                  simp only [evalExprTerm] at h
                  exact ⟨2, by unfold_eval; simp only [happ]; exact h⟩
          | error msg =>
              simp only [happ, exprCont] at h
              exact ⟨2, by unfold_eval; simp only [happ]; exact h⟩
      | next st₁ arg' =>
          rw [stepExpr_builtin_arg_next hsub] at h
          simp only [exprCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
          | succ fb' =>
              simp only [evalExprTerm] at h
              cases hsub2 : evalExprTerm fb' st₁ arg' <;>
                first
                | (simp only [hsub2] at h; exact notFuelE h hnf)
                | (obtain ⟨f₁, hf₁⟩ := antiExpr arg (st := st) (fb := fb')
                     (by simpa [hsub, exprCont] using hsub2)
                     (by simp [EvalResultNotFuel])
                   simp only [hsub2] at h
                   exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩)
      | control st₁ c =>
          rw [stepExpr_builtin_arg_control hsub] at h
          simp only [exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr arg (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepExpr_builtin_arg_error hsub] at h
          simp only [exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr arg (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
  | .paren body => by
      rename_i st fb r; intro h hnf
      cases hsub : stepExpr st body with
      | value st₁ v =>
          obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub
          simp only [stepExpr, exprCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
          | succ fb' =>
              simp only [evalExprTerm] at h
              exact ⟨2, by unfold_eval; exact h⟩
      | next st₁ body' =>
          rw [stepExpr_paren_next hsub] at h
          simp only [exprCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
          | succ fb' =>
              simp only [evalExprTerm] at h
              obtain ⟨f₁, hf₁⟩ := antiExpr body (st := st) (fb := fb')
                (by simpa [hsub, exprCont] using h) hnf
              exact ⟨f₁ + 1, by unfold_eval; exact hf₁⟩
      | control st₁ c =>
          rw [stepExpr_paren_control hsub] at h
          simp only [exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr body (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepExpr_paren_error hsub] at h
          simp only [exprCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr body (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalExprTerm]; simp only [hf₁]; exact h⟩
termination_by e => sizeOf e

theorem antiLVal : (lv : LValTerm) → ∀ {st fb r},
    lvalCont fb (stepLVal st lv) = r → EvalResultNotFuel r →
    ∃ fb2, evalLValTerm fb2 st lv = r
  | .target t => by
      rename_i st fb r; intro h hnf
      simp only [stepLVal, lvalCont] at h
      exact ⟨1, h⟩
  | .var name => by
      rename_i st fb r; intro h hnf
      simp only [stepLVal, lvalCont] at h
      cases fb with
      | zero => exact notFuelE (by simpa [evalLValTerm] using h) hnf
      | succ fb' => simp only [evalLValTerm] at h; exact ⟨1, h⟩
  | .special v => by
      rename_i st fb r; intro h hnf
      simp only [stepLVal, lvalCont] at h
      cases fb with
      | zero => exact notFuelE (by simpa [evalLValTerm] using h) hnf
      | succ fb' => simp only [evalLValTerm] at h; exact ⟨1, h⟩
  | .array name index => by
      rename_i st fb r; intro h hnf
      cases hsub : stepExpr st index with
      | value st₁ v =>
          obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub
          simp only [stepLVal] at h
          cases hidx : indexOfNum? v with
          | ok idx =>
              cases hens : ensureArrayId st name with
              | mk st₂ id =>
                  simp only [hidx, hens, lvalCont] at h
                  cases fb with
                  | zero => exact notFuelE (by simpa [evalLValTerm] using h) hnf
                  | succ fb' =>
                      simp only [evalLValTerm] at h
                      exact ⟨2, by rw [evalLValTerm]; simp only [evalExprTerm, hidx, hens]; exact h⟩
          | error msg =>
              simp only [hidx, lvalCont] at h
              exact ⟨2, by rw [evalLValTerm]; simp only [evalExprTerm, hidx]; exact h⟩
      | next st₁ index' =>
          rw [stepLVal_array_next hsub] at h
          simp only [lvalCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalLValTerm] using h) hnf
          | succ fb' =>
              simp only [evalLValTerm] at h
              cases hsub2 : evalExprTerm fb' st₁ index' <;>
                first
                | (simp only [hsub2] at h; exact notFuelE h hnf)
                | (obtain ⟨f₁, hf₁⟩ := antiExpr index (st := st) (fb := fb')
                     (by simpa [hsub, exprCont] using hsub2)
                     (by simp [EvalResultNotFuel])
                   simp only [hsub2] at h
                   exact ⟨f₁ + 1, by rw [evalLValTerm]; simp only [hf₁]; exact h⟩)
      | control st₁ c =>
          rw [stepLVal_array_control hsub] at h
          simp only [lvalCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr index (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalLValTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepLVal_array_error hsub] at h
          simp only [lvalCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr index (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalLValTerm]; simp only [hf₁]; exact h⟩
termination_by lv => sizeOf lv

theorem antiArgs : (as : List ArgTerm) → ∀ {st fb r},
    argsCont fb (stepArgs st as) = r → EvalResultNotFuel r →
    ∃ fb2, evalArgTerms fb2 st as = r
  | [] => by
      rename_i st fb r; intro h hnf
      simp only [stepArgs, argsCont] at h
      exact ⟨1, h⟩
  | .arrayRef name :: rest => by
      rename_i st fb r; intro h hnf
      cases hsub : stepArgs st rest with
      | next st₁ rest' =>
          rw [stepArgs_arrayRef_tail_next hsub] at h
          simp only [argsCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalArgTerms] using h) hnf
          | succ fb' =>
              simp only [evalArgTerms] at h
              cases hsub2 : evalArgTerms fb' st₁ rest' <;>
                first
                | (simp only [hsub2] at h; exact notFuelE h hnf)
                | (obtain ⟨f₁, hf₁⟩ := antiArgs rest (st := st) (fb := fb')
                     (by simpa [hsub, argsCont] using hsub2)
                     (by simp [EvalResultNotFuel])
                   simp only [hsub2] at h
                   exact ⟨f₁ + 1, by rw [evalArgTerms]; simp only [hf₁]; exact h⟩)
      | values st₁ vs =>
          rw [stepArgs_arrayRef_tail_values hsub] at h
          simp only [argsCont] at h
          obtain ⟨f₁, hf₁⟩ := antiArgs rest (st := st) (fb := fb)
            (by rw [hsub]) (by simp [argsCont, EvalResultNotFuel])
          simp only [argsCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalArgTerms]; simp only [hf₁]; exact h⟩
      | control st₁ c =>
          rw [stepArgs_arrayRef_tail_control hsub] at h
          simp only [argsCont] at h
          obtain ⟨f₁, hf₁⟩ := antiArgs rest (st := st) (fb := fb)
            (by rw [hsub]) (by simp [argsCont, EvalResultNotFuel])
          simp only [argsCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalArgTerms]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepArgs_arrayRef_tail_error hsub] at h
          simp only [argsCont] at h
          obtain ⟨f₁, hf₁⟩ := antiArgs rest (st := st) (fb := fb)
            (by rw [hsub]) (by simp [argsCont, EvalResultNotFuel])
          simp only [argsCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalArgTerms]; simp only [hf₁]; exact h⟩
  | .expr e :: rest => by
      rename_i st fb r; intro h hnf
      cases hsub : stepExpr st e with
      | value st₁ v =>
          obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub
          cases hsub2 : stepArgs st rest with
          | next st₁ rest' =>
              rw [stepArgs_expr_value_tail_next hsub2] at h
              simp only [argsCont] at h
              cases fb with
              | zero => exact notFuelE (by simpa [evalArgTerms] using h) hnf
              | succ fb' =>
                  simp only [evalArgTerms] at h
                  cases fb' with
                  | zero => exact notFuelE (by simpa [evalExprTerm] using h) hnf
                  | succ k =>
                      rw [evalExprTerm] at h
                      simp only [] at h
                      cases hsub3 : evalArgTerms (k + 1) st₁ rest' <;>
                        first
                        | (simp only [hsub3] at h; exact notFuelE h hnf)
                        | (obtain ⟨f₁, hf₁⟩ := antiArgs rest (st := st) (fb := k + 1)
                             (by simpa [hsub2, argsCont] using hsub3)
                             (by simp [EvalResultNotFuel])
                           simp only [hsub3] at h
                           exact ⟨f₁ + 2, by
                             unfold_eval
                             simp only [evalArgTerms_mono (show f₁ ≤ f₁ + 1 by omega) hf₁ (by simp [EvalResultNotFuel])]
                             exact h⟩)
          | values st₁ vs =>
              rw [stepArgs_expr_value_tail_values hsub2] at h
              simp only [argsCont] at h
              obtain ⟨f₁, hf₁⟩ := antiArgs rest (st := st) (fb := fb)
                (by rw [hsub2]) (by simp [argsCont, EvalResultNotFuel])
              simp only [argsCont] at hf₁
              exact ⟨f₁ + 2, by
                unfold_eval
                simp only [evalArgTerms_mono (show f₁ ≤ f₁ + 1 by omega) hf₁ (by simp [EvalResultNotFuel])]
                exact h⟩
          | control st₁ c =>
              rw [stepArgs_expr_value_tail_control hsub2] at h
              simp only [argsCont] at h
              obtain ⟨f₁, hf₁⟩ := antiArgs rest (st := st) (fb := fb)
                (by rw [hsub2]) (by simp [argsCont, EvalResultNotFuel])
              simp only [argsCont] at hf₁
              exact ⟨f₁ + 2, by
                unfold_eval
                simp only [evalArgTerms_mono (show f₁ ≤ f₁ + 1 by omega) hf₁ (by simp [EvalResultNotFuel])]
                exact h⟩
          | runtimeError st₁ msg =>
              rw [stepArgs_expr_value_tail_error hsub2] at h
              simp only [argsCont] at h
              obtain ⟨f₁, hf₁⟩ := antiArgs rest (st := st) (fb := fb)
                (by rw [hsub2]) (by simp [argsCont, EvalResultNotFuel])
              simp only [argsCont] at hf₁
              exact ⟨f₁ + 2, by
                unfold_eval
                simp only [evalArgTerms_mono (show f₁ ≤ f₁ + 1 by omega) hf₁ (by simp [EvalResultNotFuel])]
                exact h⟩
      | next st₁ e' =>
          rw [stepArgs_expr_head_next hsub] at h
          simp only [argsCont] at h
          cases fb with
          | zero => exact notFuelE (by simpa [evalArgTerms] using h) hnf
          | succ fb' =>
              simp only [evalArgTerms] at h
              cases hsub2 : evalExprTerm fb' st₁ e' with
              | outOfFuel stx => simp only [hsub2] at h; exact notFuelE h hnf
              | ok st₂ v =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr e (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  cases hsub3 : evalArgTerms fb' st₂ rest <;>
                    first
                    | (simp only [hsub3] at h; exact notFuelE h hnf)
                    | (simp only [hsub3] at h
                       refine ⟨max f₁ fb' + 1, ?_⟩
                       rw [evalArgTerms]
                       simp only [monoE (show f₁ ≤ max f₁ fb' by omega) hf₁ (by simp [EvalResultNotFuel]), evalArgTerms_mono (show fb' ≤ max f₁ fb' by omega) hsub3 (by simp [EvalResultNotFuel])]
                       exact h)
              | control st₂ c =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr e (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalArgTerms]; simp only [hf₁]; exact h⟩
              | runtimeError st₂ msg =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr e (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalArgTerms]; simp only [hf₁]; exact h⟩
      | control st₁ c =>
          rw [stepArgs_expr_head_control hsub] at h
          simp only [argsCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr e (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalArgTerms]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepArgs_expr_head_error hsub] at h
          simp only [argsCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr e (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalArgTerms]; simp only [hf₁]; exact h⟩
termination_by as => sizeOf as

theorem antiStmt : (s : StmtTerm) → ∀ {st fb r},
    stmtCont fb (stepStmt st s) = r → ResultNotFuel r →
    ∃ fb2, evalStmtTerm fb2 st s = r
  | .done => by
      rename_i st fb r; intro h hnf
      simp only [stepStmt, stmtCont] at h
      exact ⟨1, h⟩
  | .expr original e => by
      rename_i st fb r; intro h hnf
      cases hsub : stepExpr st e with
      | value st₁ v =>
          obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub
          simp only [stepStmt] at h
          cases hta : isTopAssignment original <;> simp only [hta] at h <;>
            simp only [Bool.false_eq_true, if_true, if_false, stmtCont] at h <;>
            exact ⟨2, by simp only [evalStmtTerm, evalExprTerm, hta]; simp; exact h⟩
      | next st₁ e' =>
          rw [stepStmt_expr_next hsub] at h
          simp only [stmtCont] at h
          cases fb with
          | zero => exact notFuelR (by simpa [evalStmtTerm] using h) hnf
          | succ fb' =>
              simp only [evalStmtTerm] at h
              cases hsub2 : evalExprTerm fb' st₁ e' <;>
                first
                | (simp only [hsub2] at h; exact notFuelR h hnf)
                | (obtain ⟨f₁, hf₁⟩ := antiExpr e (st := st) (fb := fb')
                     (by simpa [hsub, exprCont] using hsub2)
                     (by simp [EvalResultNotFuel])
                   simp only [hsub2] at h
                   exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩)
      | control st₁ c =>
          rw [stepStmt_expr_control hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr e (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepStmt_expr_error hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr e (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
  | .eval e => by
      rename_i st fb r; intro h hnf
      cases hsub : stepExpr st e with
      | value st₁ v =>
          obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub
          simp only [stepStmt, stmtCont] at h
          exact ⟨2, by unfold_eval; exact h⟩
      | next st₁ e' =>
          rw [stepStmt_eval_next hsub] at h
          simp only [stmtCont] at h
          cases fb with
          | zero => exact notFuelR (by simpa [evalStmtTerm] using h) hnf
          | succ fb' =>
              simp only [evalStmtTerm] at h
              cases hsub2 : evalExprTerm fb' st₁ e' <;>
                first
                | (simp only [hsub2] at h; exact notFuelR h hnf)
                | (obtain ⟨f₁, hf₁⟩ := antiExpr e (st := st) (fb := fb')
                     (by simpa [hsub, exprCont] using hsub2)
                     (by simp [EvalResultNotFuel])
                   simp only [hsub2] at h
                   exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩)
      | control st₁ c =>
          rw [stepStmt_eval_control hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr e (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepStmt_eval_error hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr e (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
  | .str sv => by
      rename_i st fb r; intro h hnf
      simp only [stepStmt, stmtCont] at h
      exact ⟨1, h⟩
  | .auto params => by
      rename_i st fb r; intro h hnf
      simp only [stepStmt, stmtCont] at h
      exact ⟨1, h⟩
  | .ifThen cond thenBranch => by
      rename_i st fb r; intro h hnf
      cases hsub : stepExpr st cond with
      | value st₁ v =>
          obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub
          simp only [stepStmt] at h
          cases hz : v.isZero with
          | true =>
              simp only [hz, if_true, stmtCont] at h
              exact ⟨2, by simp only [evalStmtTerm, evalExprTerm, hz]; simp; exact h⟩
          | false =>
              simp only [hz, Bool.false_eq_true, if_false, stmtCont] at h
              refine ⟨fb + 2, ?_⟩
              simp only [evalStmtTerm, evalExprTerm, hz]
              simp only [Bool.false_eq_true, if_false]
              exact evalStmtTerm_mono (show fb ≤ fb + 1 by omega) h hnf
      | next st₁ cond' =>
          rw [stepStmt_if_next hsub] at h
          simp only [stmtCont] at h
          cases fb with
          | zero => exact notFuelR (by simpa [evalStmtTerm] using h) hnf
          | succ fb' =>
              simp only [evalStmtTerm] at h
              cases hsub2 : evalExprTerm fb' st₁ cond' with
              | outOfFuel stx => simp only [hsub2] at h; exact notFuelR h hnf
              | ok st₂ v =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr cond (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  cases hz : v.isZero with
                  | true =>
                      simp only [hz, if_true] at h
                      exact ⟨max f₁ fb' + 1, by
                        rw [evalStmtTerm]
                        simp only [monoE (show f₁ ≤ max f₁ fb' by omega) hf₁ (by simp [EvalResultNotFuel]), hz]
                        simp
                        exact h⟩
                  | false =>
                      simp only [hz, Bool.false_eq_true, if_false] at h
                      refine ⟨max f₁ fb' + 1, ?_⟩
                      rw [evalStmtTerm]
                      simp only [monoE (show f₁ ≤ max f₁ fb' by omega) hf₁ (by simp [EvalResultNotFuel]), hz]
                      simp only [Bool.false_eq_true, if_false]
                      exact evalStmtTerm_mono (show fb' ≤ max f₁ fb' by omega) h hnf
              | control st₂ c =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr cond (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
              | runtimeError st₂ msg =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr cond (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
      | control st₁ c =>
          rw [stepStmt_if_control hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr cond (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepStmt_if_error hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr cond (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
  | .while condSource cond body => by
      rename_i st fb r; intro h hnf
      cases hsub : stepExpr st cond with
      | value st₁ v =>
          obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub
          simp only [stepStmt] at h
          cases hz : v.isZero with
          | true =>
              simp only [hz, if_true, stmtCont] at h
              exact ⟨2, by simp only [evalStmtTerm, evalExprTerm, hz]; simp; exact h⟩
          | false =>
              simp only [hz, Bool.false_eq_true, if_false, stmtCont] at h
              refine ⟨fb + 2, ?_⟩
              simp only [evalStmtTerm, evalExprTerm, hz]
              simp only [Bool.false_eq_true, if_false]
              exact evalStmtTerm_mono (show fb ≤ fb + 1 by omega) h hnf
      | next st₁ cond' =>
          rw [stepStmt_while_next hsub] at h
          simp only [stmtCont] at h
          cases fb with
          | zero => exact notFuelR (by simpa [evalStmtTerm] using h) hnf
          | succ fb' =>
              simp only [evalStmtTerm] at h
              cases hsub2 : evalExprTerm fb' st₁ cond' with
              | outOfFuel stx => simp only [hsub2] at h; exact notFuelR h hnf
              | ok st₂ v =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr cond (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  cases hz : v.isZero with
                  | true =>
                      simp only [hz, if_true] at h
                      exact ⟨max f₁ fb' + 1, by
                        rw [evalStmtTerm]
                        simp only [monoE (show f₁ ≤ max f₁ fb' by omega) hf₁ (by simp [EvalResultNotFuel]), hz]
                        simp
                        exact h⟩
                  | false =>
                      simp only [hz, Bool.false_eq_true, if_false] at h
                      refine ⟨max f₁ fb' + 1, ?_⟩
                      rw [evalStmtTerm]
                      simp only [monoE (show f₁ ≤ max f₁ fb' by omega) hf₁ (by simp [EvalResultNotFuel]), hz]
                      simp only [Bool.false_eq_true, if_false]
                      exact evalStmtTerm_mono (show fb' ≤ max f₁ fb' by omega) h hnf
              | control st₂ c =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr cond (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
              | runtimeError st₂ msg =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr cond (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
      | control st₁ c =>
          rw [stepStmt_while_control hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr cond (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepStmt_while_error hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr cond (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
  | .forCheck condSource cond updateSource body => by
      rename_i st fb r; intro h hnf
      cases hsub : stepExpr st cond with
      | value st₁ v =>
          obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub
          simp only [stepStmt] at h
          cases hz : v.isZero with
          | true =>
              simp only [hz, if_true, stmtCont] at h
              exact ⟨2, by simp only [evalStmtTerm, evalExprTerm, hz]; simp; exact h⟩
          | false =>
              simp only [hz, Bool.false_eq_true, if_false, stmtCont] at h
              refine ⟨fb + 2, ?_⟩
              simp only [evalStmtTerm, evalExprTerm, hz]
              simp only [Bool.false_eq_true, if_false]
              exact evalStmtTerm_mono (show fb ≤ fb + 1 by omega) h hnf
      | next st₁ cond' =>
          rw [stepStmt_forCheck_next hsub] at h
          simp only [stmtCont] at h
          cases fb with
          | zero => exact notFuelR (by simpa [evalStmtTerm] using h) hnf
          | succ fb' =>
              simp only [evalStmtTerm] at h
              cases hsub2 : evalExprTerm fb' st₁ cond' with
              | outOfFuel stx => simp only [hsub2] at h; exact notFuelR h hnf
              | ok st₂ v =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr cond (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  cases hz : v.isZero with
                  | true =>
                      simp only [hz, if_true] at h
                      exact ⟨max f₁ fb' + 1, by
                        rw [evalStmtTerm]
                        simp only [monoE (show f₁ ≤ max f₁ fb' by omega) hf₁ (by simp [EvalResultNotFuel]), hz]
                        simp
                        exact h⟩
                  | false =>
                      simp only [hz, Bool.false_eq_true, if_false] at h
                      refine ⟨max f₁ fb' + 1, ?_⟩
                      rw [evalStmtTerm]
                      simp only [monoE (show f₁ ≤ max f₁ fb' by omega) hf₁ (by simp [EvalResultNotFuel]), hz]
                      simp only [Bool.false_eq_true, if_false]
                      exact evalStmtTerm_mono (show fb' ≤ max f₁ fb' by omega) h hnf
              | control st₂ c =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr cond (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
              | runtimeError st₂ msg =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr cond (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
      | control st₁ c =>
          rw [stepStmt_forCheck_control hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr cond (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepStmt_forCheck_error hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr cond (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
  | .forUpdate condSource updateSource update body => by
      rename_i st fb r; intro h hnf
      cases hsub : stepExpr st update with
      | value st₁ v =>
          obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub
          simp only [stepStmt, stmtCont] at h
          refine ⟨fb + 2, ?_⟩
          simp only [evalStmtTerm, evalExprTerm]
          exact evalStmtTerm_mono (show fb ≤ fb + 1 by omega) h hnf
      | next st₁ update' =>
          rw [stepStmt_forUpdate_next hsub] at h
          simp only [stmtCont] at h
          cases fb with
          | zero => exact notFuelR (by simpa [evalStmtTerm] using h) hnf
          | succ fb' =>
              simp only [evalStmtTerm] at h
              cases hsub2 : evalExprTerm fb' st₁ update' with
              | outOfFuel stx => simp only [hsub2] at h; exact notFuelR h hnf
              | ok st₂ v =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr update (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  refine ⟨max f₁ fb' + 1, ?_⟩
                  rw [evalStmtTerm]
                  simp only [monoE (show f₁ ≤ max f₁ fb' by omega) hf₁ (by simp [EvalResultNotFuel])]
                  exact evalStmtTerm_mono (show fb' ≤ max f₁ fb' by omega) h hnf
              | control st₂ c =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr update (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
              | runtimeError st₂ msg =>
                  obtain ⟨f₁, hf₁⟩ := antiExpr update (st := st) (fb := fb')
                    (by simpa [hsub, exprCont] using hsub2)
                    (by simp [EvalResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
      | control st₁ c =>
          rw [stepStmt_forUpdate_control hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr update (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepStmt_forUpdate_error hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr update (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
  | .loopBody body after => by
      rename_i st fb r; intro h hnf
      cases hsub : stepStmt st body with
      | next st₁ body' =>
          rw [stepStmt_loop_next hsub] at h
          simp only [stmtCont] at h
          cases fb with
          | zero => exact notFuelR (by simpa [evalStmtTerm] using h) hnf
          | succ fb' =>
              simp only [evalStmtTerm] at h
              cases hsub2 : evalStmtTerm fb' st₁ body' with
              | outOfFuel stx => simp only [hsub2] at h; exact notFuelR h hnf
              | ok stB c =>
                  obtain ⟨f₁, hf₁⟩ := antiStmt body (st := st) (fb := fb')
                    (by simpa [hsub, stmtCont] using hsub2)
                    (by simp [ResultNotFuel])
                  simp only [hsub2] at h
                  cases c with
                  | normal =>
                      refine ⟨max f₁ fb' + 1, ?_⟩
                      rw [evalStmtTerm]
                      simp only [evalStmtTerm_mono (show f₁ ≤ max f₁ fb' by omega) hf₁ (by simp [ResultNotFuel])]
                      exact evalStmtTerm_mono (show fb' ≤ max f₁ fb' by omega) h hnf
                  | «break» =>
                      exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
                  | «return» v? =>
                      exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
                  | quit =>
                      exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
              | runtimeError stB msg =>
                  obtain ⟨f₁, hf₁⟩ := antiStmt body (st := st) (fb := fb')
                    (by simpa [hsub, stmtCont] using hsub2)
                    (by simp [ResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
      | done st₁ =>
          rw [stepStmt_loop_done hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiStmt body (st := st) (fb := fb)
            (by rw [hsub]) (by simp [stmtCont, ResultNotFuel])
          simp only [stmtCont] at hf₁
          refine ⟨max f₁ fb + 1, ?_⟩
          rw [evalStmtTerm]
          simp only [evalStmtTerm_mono (show f₁ ≤ max f₁ fb by omega) hf₁ (by simp [ResultNotFuel])]
          exact evalStmtTerm_mono (show fb ≤ max f₁ fb by omega) h hnf
      | control st₁ c =>
          obtain ⟨f₁, hf₁⟩ := antiStmt body (st := st) (fb := fb)
            (by rw [hsub]) (by simp [stmtCont, ResultNotFuel])
          simp only [stmtCont] at hf₁
          cases c with
          | normal => exact absurd rfl (stepStmt_control_ne_normal hsub)
          | «break» =>
              rw [stepStmt_loop_break hsub] at h
              simp only [stmtCont] at h
              exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
          | «return» v? =>
              rw [stepStmt_loop_control (by intro hc; cases hc) hsub] at h
              simp only [stmtCont] at h
              exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
          | quit =>
              rw [stepStmt_loop_control (by intro hc; cases hc) hsub] at h
              simp only [stmtCont] at h
              exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepStmt_loop_error hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiStmt body (st := st) (fb := fb)
            (by rw [hsub]) (by simp [stmtCont, ResultNotFuel])
          simp only [stmtCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
  | .seq first second => by
      rename_i st fb r; intro h hnf
      cases hsub : stepStmt st first with
      | next st₁ first' =>
          rw [stepStmt_seq_next hsub] at h
          simp only [stmtCont] at h
          cases fb with
          | zero => exact notFuelR (by simpa [evalStmtTerm] using h) hnf
          | succ fb' =>
              simp only [evalStmtTerm] at h
              cases hsub2 : evalStmtTerm fb' st₁ first' with
              | outOfFuel stx => simp only [hsub2] at h; exact notFuelR h hnf
              | ok stB c =>
                  obtain ⟨f₁, hf₁⟩ := antiStmt first (st := st) (fb := fb')
                    (by simpa [hsub, stmtCont] using hsub2)
                    (by simp [ResultNotFuel])
                  simp only [hsub2] at h
                  cases c with
                  | normal =>
                      refine ⟨max f₁ fb' + 1, ?_⟩
                      rw [evalStmtTerm]
                      simp only [evalStmtTerm_mono (show f₁ ≤ max f₁ fb' by omega) hf₁ (by simp [ResultNotFuel])]
                      exact evalStmtTerm_mono (show fb' ≤ max f₁ fb' by omega) h hnf
                  | «break» =>
                      exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
                  | «return» v? =>
                      exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
                  | quit =>
                      exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
              | runtimeError stB msg =>
                  obtain ⟨f₁, hf₁⟩ := antiStmt first (st := st) (fb := fb')
                    (by simpa [hsub, stmtCont] using hsub2)
                    (by simp [ResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
      | done st₁ =>
          rw [stepStmt_seq_done hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiStmt first (st := st) (fb := fb)
            (by rw [hsub]) (by simp [stmtCont, ResultNotFuel])
          simp only [stmtCont] at hf₁
          refine ⟨max f₁ fb + 1, ?_⟩
          rw [evalStmtTerm]
          simp only [evalStmtTerm_mono (show f₁ ≤ max f₁ fb by omega) hf₁ (by simp [ResultNotFuel])]
          exact evalStmtTerm_mono (show fb ≤ max f₁ fb by omega) h hnf
      | control st₁ c =>
          rw [stepStmt_seq_control hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiStmt first (st := st) (fb := fb)
            (by rw [hsub]) (by simp [stmtCont, ResultNotFuel])
          simp only [stmtCont] at hf₁
          cases c with
          | normal => exact absurd rfl (stepStmt_control_ne_normal hsub)
          | «break» =>
              exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
          | «return» v? =>
              exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
          | quit =>
              exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepStmt_seq_error hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiStmt first (st := st) (fb := fb)
            (by rw [hsub]) (by simp [stmtCont, ResultNotFuel])
          simp only [stmtCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
  | .break => by
      rename_i st fb r; intro h hnf
      simp only [stepStmt, stmtCont] at h
      exact ⟨1, h⟩
  | .return none => by
      rename_i st fb r; intro h hnf
      simp only [stepStmt, stmtCont] at h
      exact ⟨1, h⟩
  | .return (some e) => by
      rename_i st fb r; intro h hnf
      cases hsub : stepExpr st e with
      | value st₁ v =>
          obtain ⟨rfl, -⟩ := stepExpr_value_inv hsub
          simp only [stepStmt, stmtCont] at h
          exact ⟨2, by unfold_eval; exact h⟩
      | next st₁ e' =>
          rw [stepStmt_return_next hsub] at h
          simp only [stmtCont] at h
          cases fb with
          | zero => exact notFuelR (by simpa [evalStmtTerm] using h) hnf
          | succ fb' =>
              simp only [evalStmtTerm] at h
              cases hsub2 : evalExprTerm fb' st₁ e' <;>
                first
                | (simp only [hsub2] at h; exact notFuelR h hnf)
                | (obtain ⟨f₁, hf₁⟩ := antiExpr e (st := st) (fb := fb')
                     (by simpa [hsub, exprCont] using hsub2)
                     (by simp [EvalResultNotFuel])
                   simp only [hsub2] at h
                   exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩)
      | control st₁ c =>
          rw [stepStmt_return_control hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr e (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          rw [stepStmt_return_error hsub] at h
          simp only [stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiExpr e (st := st) (fb := fb)
            (by rw [hsub]) (by simp [exprCont, EvalResultNotFuel])
          simp only [exprCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalStmtTerm]; simp only [hf₁]; exact h⟩
  | .quit => by
      rename_i st fb r; intro h hnf
      simp only [stepStmt, stmtCont] at h
      exact ⟨1, h⟩
  | .block body => by
      rename_i st fb r; intro h hnf
      simp only [stepStmt] at h
      cases hsub : stepBody st body with
      | next st₁ body' =>
          simp only [hsub, stmtCont] at h
          cases fb with
          | zero => exact notFuelR (by simpa [evalStmtTerm] using h) hnf
          | succ fb' =>
              simp only [evalStmtTerm] at h
              obtain ⟨f₁, hf₁⟩ := antiBody body (st := st) (fb := fb')
                (by simpa [hsub, bodyCont] using h) hnf
              exact ⟨f₁ + 1, by rw [evalStmtTerm]; exact hf₁⟩
      | done st₁ =>
          simp only [hsub, stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiBody body (st := st) (fb := fb)
            (by rw [hsub]) (by simp [bodyCont, ResultNotFuel])
          simp only [bodyCont] at hf₁
          exact ⟨f₁ + 1, by simp only [evalStmtTerm]; rw [hf₁]; exact h⟩
      | control st₁ c =>
          simp only [hsub, stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiBody body (st := st) (fb := fb)
            (by rw [hsub]) (by simp [bodyCont, ResultNotFuel])
          simp only [bodyCont] at hf₁
          exact ⟨f₁ + 1, by simp only [evalStmtTerm]; rw [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          simp only [hsub, stmtCont] at h
          obtain ⟨f₁, hf₁⟩ := antiBody body (st := st) (fb := fb)
            (by rw [hsub]) (by simp [bodyCont, ResultNotFuel])
          simp only [bodyCont] at hf₁
          exact ⟨f₁ + 1, by simp only [evalStmtTerm]; rw [hf₁]; exact h⟩
termination_by s => sizeOf s

theorem antiBody : (b : BodyTerm) → ∀ {st fb r},
    bodyCont fb (stepBody st b) = r → ResultNotFuel r →
    ∃ fb2, evalBodyTerm fb2 st b = r
  | .stmts [] => by
      rename_i st fb r; intro h hnf
      simp only [stepBody, bodyCont] at h
      exact ⟨1, h⟩
  | .stmts (s :: rest) => by
      rename_i st fb r; intro h hnf
      cases hsub : stepStmt st s with
      | next st₁ s' =>
          simp only [stepBody, hsub, bodyCont] at h
          cases fb with
          | zero => exact notFuelR (by simpa [evalBodyTerm] using h) hnf
          | succ fb' =>
              simp only [evalBodyTerm] at h
              cases hsub2 : evalStmtTerm fb' st₁ s' with
              | outOfFuel stx => simp only [hsub2] at h; exact notFuelR h hnf
              | ok stB c =>
                  obtain ⟨f₁, hf₁⟩ := antiStmt s (st := st) (fb := fb')
                    (by simpa [hsub, stmtCont] using hsub2)
                    (by simp [ResultNotFuel])
                  simp only [hsub2] at h
                  cases c with
                  | normal =>
                      refine ⟨max f₁ fb' + 1, ?_⟩
                      rw [evalBodyTerm]
                      simp only [evalStmtTerm_mono (show f₁ ≤ max f₁ fb' by omega) hf₁ (by simp [ResultNotFuel])]
                      exact evalBodyTerm_mono (show fb' ≤ max f₁ fb' by omega) h hnf
                  | «break» =>
                      exact ⟨f₁ + 1, by rw [evalBodyTerm]; simp only [hf₁]; exact h⟩
                  | «return» v? =>
                      exact ⟨f₁ + 1, by rw [evalBodyTerm]; simp only [hf₁]; exact h⟩
                  | quit =>
                      exact ⟨f₁ + 1, by rw [evalBodyTerm]; simp only [hf₁]; exact h⟩
              | runtimeError stB msg =>
                  obtain ⟨f₁, hf₁⟩ := antiStmt s (st := st) (fb := fb')
                    (by simpa [hsub, stmtCont] using hsub2)
                    (by simp [ResultNotFuel])
                  simp only [hsub2] at h
                  exact ⟨f₁ + 1, by rw [evalBodyTerm]; simp only [hf₁]; exact h⟩
      | done st₁ =>
          simp only [stepBody, hsub, bodyCont] at h
          obtain ⟨f₁, hf₁⟩ := antiStmt s (st := st) (fb := fb)
            (by rw [hsub]) (by simp [stmtCont, ResultNotFuel])
          simp only [stmtCont] at hf₁
          refine ⟨max f₁ fb + 1, ?_⟩
          rw [evalBodyTerm]
          simp only [evalStmtTerm_mono (show f₁ ≤ max f₁ fb by omega) hf₁ (by simp [ResultNotFuel])]
          exact evalBodyTerm_mono (show fb ≤ max f₁ fb by omega) h hnf
      | control st₁ c =>
          simp only [stepBody, hsub, bodyCont] at h
          obtain ⟨f₁, hf₁⟩ := antiStmt s (st := st) (fb := fb)
            (by rw [hsub]) (by simp [stmtCont, ResultNotFuel])
          simp only [stmtCont] at hf₁
          cases c with
          | normal => exact absurd rfl (stepStmt_control_ne_normal hsub)
          | «break» =>
              exact ⟨f₁ + 1, by rw [evalBodyTerm]; simp only [hf₁]; exact h⟩
          | «return» v? =>
              exact ⟨f₁ + 1, by rw [evalBodyTerm]; simp only [hf₁]; exact h⟩
          | quit =>
              exact ⟨f₁ + 1, by rw [evalBodyTerm]; simp only [hf₁]; exact h⟩
      | runtimeError st₁ msg =>
          simp only [stepBody, hsub, bodyCont] at h
          obtain ⟨f₁, hf₁⟩ := antiStmt s (st := st) (fb := fb)
            (by rw [hsub]) (by simp [stmtCont, ResultNotFuel])
          simp only [stmtCont] at hf₁
          exact ⟨f₁ + 1, by rw [evalBodyTerm]; simp only [hf₁]; exact h⟩
termination_by b => sizeOf b

end

/-! ### Backward: finite small-step runs are reproduced by the residual interpreter -/

/-- Final result of a statement outcome (the `next` case cannot occur for
finished runs). -/
def stmtFromOutcome : StmtOutcome → Result Control
  | .next st _ => .runtimeError st "internal next in stmtFromOutcome"
  | .done st => .ok st .normal
  | .control st c => .ok st c
  | .runtimeError st msg => .runtimeError st msg

/-- Final result of a body outcome. -/
def bodyFromOutcome : BodyOutcome → Result Control
  | .next st _ => .runtimeError st "internal next in bodyFromOutcome"
  | .done st => .ok st .normal
  | .control st c => .ok st c
  | .runtimeError st msg => .runtimeError st msg

private theorem exprFromOutcome_notFuel (o : ExprOutcome) :
    EvalResultNotFuel (exprFromOutcome o) := by
  cases o <;> simp [exprFromOutcome, EvalResultNotFuel]

private theorem stmtFromOutcome_notFuel (o : StmtOutcome) :
    ResultNotFuel (stmtFromOutcome o) := by
  cases o <;> simp [stmtFromOutcome, ResultNotFuel]

private theorem bodyFromOutcome_notFuel (o : BodyOutcome) :
    ResultNotFuel (bodyFromOutcome o) := by
  cases o <;> simp [bodyFromOutcome, ResultNotFuel]

theorem ExprRuns.to_eval {st e o} (h : ExprRuns st e o) :
    ∃ fb, evalExprTerm fb st e = exprFromOutcome o := by
  induction h with
  | value => exact ⟨1, rfl⟩
  | control hstep =>
      exact antiExpr _ (fb := 0) (by rw [hstep]; rfl)
        (by simp [exprFromOutcome, EvalResultNotFuel])
  | runtimeError hstep =>
      exact antiExpr _ (fb := 0) (by rw [hstep]; rfl)
        (by simp [exprFromOutcome, EvalResultNotFuel])
  | next hstep _ ih =>
      obtain ⟨fb, hfb⟩ := ih
      exact antiExpr _ (fb := fb) (by rw [hstep]; exact hfb) (exprFromOutcome_notFuel _)

theorem StmtRuns.to_eval {st s o} (h : StmtRuns st s o) :
    ∃ fb, evalStmtTerm fb st s = stmtFromOutcome o := by
  induction h with
  | stop hstep hfinal =>
      rename_i st' s' o'
      cases o' with
      | next stx sx => exact absurd hfinal (by simp [StmtFinal])
      | done stx =>
          exact antiStmt _ (fb := 0) (by rw [hstep]; rfl)
            (by simp [stmtFromOutcome, ResultNotFuel])
      | control stx c =>
          exact antiStmt _ (fb := 0) (by rw [hstep]; rfl)
            (by simp [stmtFromOutcome, ResultNotFuel])
      | runtimeError stx msg =>
          exact antiStmt _ (fb := 0) (by rw [hstep]; rfl)
            (by simp [stmtFromOutcome, ResultNotFuel])
  | next hstep _ ih =>
      obtain ⟨fb, hfb⟩ := ih
      exact antiStmt _ (fb := fb) (by rw [hstep]; exact hfb) (stmtFromOutcome_notFuel _)

theorem BodyRuns.to_eval {st b o} (h : BodyRuns st b o) :
    ∃ fb, evalBodyTerm fb st b = bodyFromOutcome o := by
  induction h with
  | stop hstep hfinal =>
      rename_i st' b' o'
      cases o' with
      | next stx bx => exact absurd hfinal (by simp [BodyFinal])
      | done stx =>
          exact antiBody _ (fb := 0) (by rw [hstep]; rfl)
            (by simp [bodyFromOutcome, ResultNotFuel])
      | control stx c =>
          exact antiBody _ (fb := 0) (by rw [hstep]; rfl)
            (by simp [bodyFromOutcome, ResultNotFuel])
      | runtimeError stx msg =>
          exact antiBody _ (fb := 0) (by rw [hstep]; rfl)
            (by simp [bodyFromOutcome, ResultNotFuel])
  | next hstep _ ih =>
      obtain ⟨fb, hfb⟩ := ih
      exact antiBody _ (fb := fb) (by rw [hstep]; exact hfb) (bodyFromOutcome_notFuel _)

end BigSmall

end Bc
