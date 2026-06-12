/-
  Fuel monotonicity of the source big-step evaluator.

  `Bc.evalExpr` and friends thread a single decreasing fuel counter; once a
  result other than `outOfFuel` is produced, supplying more fuel cannot change
  it.  Used by the backward simulation to combine fuels of sub-evaluations.
-/

import Bc.BigStep
import Bc.BigSmall.Forward

namespace Bc

namespace BigSmall

set_option maxHeartbeats 1000000

structure SrcMonoProps (n : Nat) : Prop where
  expr : ∀ {m st e r}, n ≤ m → evalExpr n st e = r → EvalResultNotFuel r →
    evalExpr m st e = r
  rel : ∀ {m st left rest r}, n ≤ m → evalRelChain n st left rest = r →
    EvalResultNotFuel r → evalRelChain m st left rest = r
  lval : ∀ {m st lv r}, n ≤ m → evalLValueTarget n st lv = r → EvalResultNotFuel r →
    evalLValueTarget m st lv = r
  assign : ∀ {m st lhs op rhs r}, n ≤ m → evalAssign n st lhs op rhs = r →
    EvalResultNotFuel r → evalAssign m st lhs op rhs = r
  unary : ∀ {m st op arg r}, n ≤ m → evalUnary n st op arg = r →
    EvalResultNotFuel r → evalUnary m st op arg = r
  builtin : ∀ {m st fn arg r}, n ≤ m → evalBuiltin n st fn arg = r →
    EvalResultNotFuel r → evalBuiltin m st fn arg = r
  args : ∀ {m st as r}, n ≤ m → evalArgValues n st as = r → EvalResultNotFuel r →
    evalArgValues m st as = r
  call : ∀ {m st name as r}, n ≤ m → evalCall n st name as = r → EvalResultNotFuel r →
    evalCall m st name as = r
  stmt : ∀ {m st s r}, n ≤ m → evalStmt n st s = r → ResultNotFuel r →
    evalStmt m st s = r
  forLoop : ∀ {m st c u b r}, n ≤ m → evalFor n st c u b = r → ResultNotFuel r →
    evalFor m st c u b = r
  stmts : ∀ {m st ss r}, n ≤ m → evalStmts n st ss = r → ResultNotFuel r →
    evalStmts m st ss = r
  body : ∀ {m st items r}, n ≤ m → evalBody n st items = r → ResultNotFuel r →
    evalBody m st items = r

private theorem srcMonoProps : ∀ n, SrcMonoProps n := by
  intro n
  induction n with
  | zero =>
      exact
        { expr := fun _ h hr => by simp [evalExpr] at h; subst h; exact absurd hr (by simp [EvalResultNotFuel])
          rel := fun _ h hr => by simp [evalRelChain] at h; subst h; exact absurd hr (by simp [EvalResultNotFuel])
          lval := fun _ h hr => by simp [evalLValueTarget] at h; subst h; exact absurd hr (by simp [EvalResultNotFuel])
          assign := fun _ h hr => by simp [evalAssign] at h; subst h; exact absurd hr (by simp [EvalResultNotFuel])
          unary := fun _ h hr => by simp [evalUnary] at h; subst h; exact absurd hr (by simp [EvalResultNotFuel])
          builtin := fun _ h hr => by simp [evalBuiltin] at h; subst h; exact absurd hr (by simp [EvalResultNotFuel])
          args := fun _ h hr => by simp [evalArgValues] at h; subst h; exact absurd hr (by simp [EvalResultNotFuel])
          call := fun _ h hr => by simp [evalCall] at h; subst h; exact absurd hr (by simp [EvalResultNotFuel])
          stmt := fun _ h hr => by simp [evalStmt] at h; subst h; exact absurd hr (by simp [ResultNotFuel])
          forLoop := fun _ h hr => by simp [evalFor] at h; subst h; exact absurd hr (by simp [ResultNotFuel])
          stmts := fun _ h hr => by simp [evalStmts] at h; subst h; exact absurd hr (by simp [ResultNotFuel])
          body := fun _ h hr => by simp [evalBody] at h; subst h; exact absurd hr (by simp [ResultNotFuel]) }
  | succ k ih =>
      have he := @SrcMonoProps.expr k ih
      have hrel := @SrcMonoProps.rel k ih
      have hl := @SrcMonoProps.lval k ih
      have hasn := @SrcMonoProps.assign k ih
      have hu := @SrcMonoProps.unary k ih
      have hbi := @SrcMonoProps.builtin k ih
      have ha := @SrcMonoProps.args k ih
      have hc := @SrcMonoProps.call k ih
      have hs := @SrcMonoProps.stmt k ih
      have hf := @SrcMonoProps.forLoop k ih
      have hss := @SrcMonoProps.stmts k ih
      have hb := @SrcMonoProps.body k ih
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro m st e r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        cases e <;> simp only [evalExpr] at h ⊢ <;>
          grind [EvalResultNotFuel, ResultNotFuel]
      · intro m st left rest r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        cases rest <;> simp only [evalRelChain] at h ⊢ <;>
          grind [EvalResultNotFuel, ResultNotFuel]
      · intro m st lv r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        cases lv <;> simp only [evalLValueTarget] at h ⊢ <;>
          grind [EvalResultNotFuel, ResultNotFuel]
      · intro m st lhs op rhs r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        simp only [evalAssign] at h ⊢
        grind [EvalResultNotFuel, ResultNotFuel]
      · intro m st op arg r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        cases op <;> simp only [evalUnary] at h ⊢ <;>
          grind [EvalResultNotFuel, ResultNotFuel]
      · intro m st fn arg r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        cases arg <;> simp only [evalBuiltin] at h ⊢ <;>
          grind [EvalResultNotFuel, ResultNotFuel]
      · intro m st as r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        match as with
        | [] => simp only [evalArgValues] at h ⊢; grind [EvalResultNotFuel, ResultNotFuel]
        | .expr e :: rest =>
            simp only [evalArgValues] at h ⊢
            grind [EvalResultNotFuel, ResultNotFuel]
        | .arrayRef nm :: rest =>
            simp only [evalArgValues] at h ⊢
            grind [EvalResultNotFuel, ResultNotFuel]
      · intro m st name as r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        simp only [evalCall] at h ⊢
        cases hlk : lookupFunction st name with
        | none => simp only [hlk] at h ⊢; exact h
        | some defn =>
            simp only [hlk] at h ⊢
            cases hav : evalArgValues k st as with
            | ok stA av =>
                rw [ha hkj hav (by simp [EvalResultNotFuel])]
                simp only [hav] at h
                grind [EvalResultNotFuel, ResultNotFuel]
            | control stA c =>
                rw [ha hkj hav (by simp [EvalResultNotFuel])]
                simpa [hav] using h
            | outOfFuel stA =>
                simp only [hav] at h
                subst h
                exact absurd hr (by simp [EvalResultNotFuel])
            | runtimeError stA msg =>
                rw [ha hkj hav (by simp [EvalResultNotFuel])]
                simpa [hav] using h
      · intro m st s r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        cases s <;> simp only [evalStmt] at h ⊢ <;>
          grind [EvalResultNotFuel, ResultNotFuel]
      · intro m st c u b r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        simp only [evalFor] at h ⊢
        cases hcond : evalExpr k st c with
        | ok stC n =>
            rw [he hkj hcond (by simp [EvalResultNotFuel])]
            simp only [hcond] at h
            grind [EvalResultNotFuel, ResultNotFuel]
        | control stC ctl =>
            rw [he hkj hcond (by simp [EvalResultNotFuel])]
            simpa [hcond] using h
        | outOfFuel stC =>
            simp only [hcond] at h
            subst h
            exact absurd hr (by simp [ResultNotFuel])
        | runtimeError stC msg =>
            rw [he hkj hcond (by simp [EvalResultNotFuel])]
            simpa [hcond] using h
      · intro m st ss r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        cases ss <;> simp only [evalStmts] at h ⊢ <;>
          grind [EvalResultNotFuel, ResultNotFuel]
      · intro m st items r hnm h hr
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hkj : k ≤ j := by omega
        match items with
        | [] => simp only [evalBody] at h ⊢; grind [EvalResultNotFuel, ResultNotFuel]
        | .newline :: rest => simp only [evalBody] at h ⊢; grind [EvalResultNotFuel, ResultNotFuel]
        | .stmts ss :: rest => simp only [evalBody] at h ⊢; grind [EvalResultNotFuel, ResultNotFuel]

theorem evalExpr_mono {n m st e r} (hnm : n ≤ m)
    (h : evalExpr n st e = r) (hr : EvalResultNotFuel r) : evalExpr m st e = r :=
  (srcMonoProps n).expr hnm h hr

theorem evalRelChain_mono {n m st left rest r} (hnm : n ≤ m)
    (h : evalRelChain n st left rest = r) (hr : EvalResultNotFuel r) :
    evalRelChain m st left rest = r :=
  (srcMonoProps n).rel hnm h hr

theorem evalLValueTarget_mono {n m st lv r} (hnm : n ≤ m)
    (h : evalLValueTarget n st lv = r) (hr : EvalResultNotFuel r) :
    evalLValueTarget m st lv = r :=
  (srcMonoProps n).lval hnm h hr

theorem evalArgValues_mono {n m st as r} (hnm : n ≤ m)
    (h : evalArgValues n st as = r) (hr : EvalResultNotFuel r) :
    evalArgValues m st as = r :=
  (srcMonoProps n).args hnm h hr

theorem evalStmt_mono {n m st s r} (hnm : n ≤ m)
    (h : evalStmt n st s = r) (hr : ResultNotFuel r) : evalStmt m st s = r :=
  (srcMonoProps n).stmt hnm h hr

theorem evalFor_mono {n m st c u b r} (hnm : n ≤ m)
    (h : evalFor n st c u b = r) (hr : ResultNotFuel r) : evalFor m st c u b = r :=
  (srcMonoProps n).forLoop hnm h hr

theorem evalStmts_mono {n m st ss r} (hnm : n ≤ m)
    (h : evalStmts n st ss = r) (hr : ResultNotFuel r) : evalStmts m st ss = r :=
  (srcMonoProps n).stmts hnm h hr

theorem evalBody_mono {n m st items r} (hnm : n ≤ m)
    (h : evalBody n st items = r) (hr : ResultNotFuel r) : evalBody m st items = r :=
  (srcMonoProps n).body hnm h hr

theorem evalTopItem_mono {n m st item r} (hnm : n ≤ m)
    (h : evalTopItem n st item = r) (hr : ResultNotFuel r) : evalTopItem m st item = r := by
  cases item with
  | funDef defn => simpa [evalTopItem] using h
  | stmts ss => exact evalStmts_mono hnm (by simpa [evalTopItem] using h) hr

theorem evalProgramItems_mono {n m st program r} (hnm : n ≤ m)
    (h : evalProgramItems n st program = r) (hr : ResultNotFuel r) :
    evalProgramItems m st program = r := by
  induction n generalizing m st program r with
  | zero =>
      simp [evalProgramItems] at h
      subst h
      exact absurd hr (by simp [ResultNotFuel])
  | succ k ihp =>
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have hkj : k ≤ j := by omega
      cases program with
      | nil => simpa [evalProgramItems] using h
      | cons item rest =>
          simp only [evalProgramItems] at h ⊢
          cases hquit : TopItem.containsQuit item with
          | true => simpa [hquit] using h
          | false =>
              simp only [hquit, Bool.false_eq_true, if_false] at h ⊢
              cases htop : evalTopItem k st item with
              | ok st₁ c =>
                  rw [evalTopItem_mono hkj htop (by simp [ResultNotFuel])]
                  simp only [htop] at h
                  cases c with
                  | normal =>
                      simp only at h ⊢
                      cases hstop : st₁.stopped with
                      | true => simpa [hstop] using h
                      | false =>
                          simp only [hstop] at h ⊢
                          exact ihp hkj h hr
                  | «break» => simpa using h
                  | «return» v => simpa using h
                  | quit => simpa using h
              | outOfFuel st₁ =>
                  simp only [htop] at h
                  subst h
                  exact absurd hr (by simp [ResultNotFuel])
              | runtimeError st₁ msg =>
                  rw [evalTopItem_mono hkj htop (by simp [ResultNotFuel])]
                  simpa [htop] using h

end BigSmall

end Bc
