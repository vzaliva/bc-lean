/-
  Backward simulation, expression/statement/body layers.

  Built on the residual interpreter `Bc/BigSmall/Residual.lean`.  The plan:

  * `ResMonoProps` — fuel monotonicity of the residual interpreter.
  * mirror lemmas — on source-shaped terms the residual interpreter agrees with
    the genuine big-step evaluator `Bc.evalExpr` &c.
  * backward lemmas — every finite `*Runs` derivation is reproduced by the
    residual interpreter (hence, via the mirror, by big-step).
-/

import Bc.BigSmall.Residual
import Bc.BigSmall.Forward

namespace Bc

namespace BigSmall

open SmallStep

set_option maxHeartbeats 1000000

/-! ### Fuel monotonicity of the residual interpreter -/

structure ResMonoProps (n : Nat) : Prop where
  expr : ∀ {m st e r}, n ≤ m → evalExprTerm n st e = r → EvalResultNotFuel r →
    evalExprTerm m st e = r
  rel : ∀ {m st left rest r}, n ≤ m → evalRelChainTerm n st left rest = r →
    EvalResultNotFuel r → evalRelChainTerm m st left rest = r
  lval : ∀ {m st lv r}, n ≤ m → evalLValTerm n st lv = r → EvalResultNotFuel r →
    evalLValTerm m st lv = r
  args : ∀ {m st a r}, n ≤ m → evalArgTerms n st a = r → EvalResultNotFuel r →
    evalArgTerms m st a = r
  stmt : ∀ {m st s r}, n ≤ m → evalStmtTerm n st s = r → ResultNotFuel r →
    evalStmtTerm m st s = r
  body : ∀ {m st b r}, n ≤ m → evalBodyTerm n st b = r → ResultNotFuel r →
    evalBodyTerm m st b = r

private theorem resMonoProps : ∀ n, ResMonoProps n := by
  intro n
  induction n with
  | zero =>
      exact
        { expr := fun _ h hr => by simp [evalExprTerm] at h; subst h; exact absurd hr (by simp [EvalResultNotFuel])
          rel := fun _ h hr => by simp [evalRelChainTerm] at h; subst h; exact absurd hr (by simp [EvalResultNotFuel])
          lval := fun _ h hr => by simp [evalLValTerm] at h; subst h; exact absurd hr (by simp [EvalResultNotFuel])
          args := fun _ h hr => by simp [evalArgTerms] at h; subst h; exact absurd hr (by simp [EvalResultNotFuel])
          stmt := fun _ h hr => by simp [evalStmtTerm] at h; subst h; exact absurd hr (by simp [ResultNotFuel])
          body := fun _ h hr => by simp [evalBodyTerm] at h; subst h; exact absurd hr (by simp [ResultNotFuel]) }
  | succ k ih =>
      have he := @ResMonoProps.expr k ih
      have hrel := @ResMonoProps.rel k ih
      have hl := @ResMonoProps.lval k ih
      have ha := @ResMonoProps.args k ih
      have hs := @ResMonoProps.stmt k ih
      have hb := @ResMonoProps.body k ih
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro m st e r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        cases e <;> simp only [evalExprTerm] at h ⊢
        case call name args =>
          cases hlk : lookupFunction st name with
          | none => grind [EvalResultNotFuel, ResultNotFuel]
          | some defn =>
              cases hav : evalArgTerms k st args with
              | ok stA av =>
                  rw [ha hkj hav (by simp [EvalResultNotFuel])]
                  grind [EvalResultNotFuel, ResultNotFuel]
              | control stA c =>
                  rw [ha hkj hav (by simp [EvalResultNotFuel])]
                  grind [EvalResultNotFuel, ResultNotFuel]
              | outOfFuel stA => grind [EvalResultNotFuel, ResultNotFuel]
              | runtimeError stA msg =>
                  rw [ha hkj hav (by simp [EvalResultNotFuel])]
                  grind [EvalResultNotFuel, ResultNotFuel]
        all_goals grind [EvalResultNotFuel, ResultNotFuel]
      · intro m st left rest r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        cases rest <;> simp only [evalRelChainTerm] at h ⊢ <;>
          grind [EvalResultNotFuel, ResultNotFuel]
      · intro m st lv r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        cases lv <;> simp only [evalLValTerm] at h ⊢ <;>
          grind [EvalResultNotFuel, ResultNotFuel]
      · intro m st a r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        match a with
        | [] => simp only [evalArgTerms] at h ⊢; grind [EvalResultNotFuel, ResultNotFuel]
        | .arrayRef _ :: _ => simp only [evalArgTerms] at h ⊢; grind [EvalResultNotFuel, ResultNotFuel]
        | .expr _ :: _ => simp only [evalArgTerms] at h ⊢; grind [EvalResultNotFuel, ResultNotFuel]
      · intro m st s r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        cases s <;> simp only [evalStmtTerm] at h ⊢ <;>
          grind [EvalResultNotFuel, ResultNotFuel]
      · intro m st b r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        match b with
        | .stmts [] => simp only [evalBodyTerm] at h ⊢; grind [EvalResultNotFuel, ResultNotFuel]
        | .stmts (_ :: _) => simp only [evalBodyTerm] at h ⊢; grind [EvalResultNotFuel, ResultNotFuel]

theorem evalExprTerm_mono {n m st e r} (hnm : n ≤ m)
    (h : evalExprTerm n st e = r) (hr : EvalResultNotFuel r) : evalExprTerm m st e = r :=
  (resMonoProps n).expr hnm h hr

theorem evalLValTerm_mono {n m st lv r} (hnm : n ≤ m)
    (h : evalLValTerm n st lv = r) (hr : EvalResultNotFuel r) : evalLValTerm m st lv = r :=
  (resMonoProps n).lval hnm h hr

theorem evalArgTerms_mono {n m st a r} (hnm : n ≤ m)
    (h : evalArgTerms n st a = r) (hr : EvalResultNotFuel r) : evalArgTerms m st a = r :=
  (resMonoProps n).args hnm h hr

theorem evalStmtTerm_mono {n m st s r} (hnm : n ≤ m)
    (h : evalStmtTerm n st s = r) (hr : ResultNotFuel r) : evalStmtTerm m st s = r :=
  (resMonoProps n).stmt hnm h hr

theorem evalBodyTerm_mono {n m st b r} (hnm : n ≤ m)
    (h : evalBodyTerm n st b = r) (hr : ResultNotFuel r) : evalBodyTerm m st b = r :=
  (resMonoProps n).body hnm h hr

end BigSmall

end Bc
