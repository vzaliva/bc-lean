/-
  Backward simulation: terminating small-step runs are reproduced by the
  big-step evaluator.

  The forward direction (`Bc/BigSmall/Forward.lean`) shows every terminating
  big-step evaluation is matched by a finite small-step run.  Here we close the
  loop.  Rather than rebuild the whole simulation in reverse, we observe that the
  small-step `step` function is deterministic, so the small-step evaluator has a
  unique final result.  Combined with the forward direction this reduces the
  backward direction to a single *termination-transfer* fact: a terminating
  small-step run guarantees the big-step evaluator also terminates.
-/

import Bc.BigSmall.Forward

namespace Bc

namespace BigSmall

open SmallStep

/-! ### Small-step final-result determinism

`runConfig` just iterates the deterministic `step` function, so once it produces
a non-`outOfFuel` result extra fuel cannot change it. -/

/-- A `RunResult` that is not the fuel-exhaustion sentinel. -/
def RunResultFinal : RunResult → Prop
  | .outOfFuel _ => False
  | _ => True

theorem runConfig_mono {c : Config} {r : RunResult} :
    ∀ {f₁ f₂ : Nat}, f₁ ≤ f₂ → runConfig f₁ c = r → RunResultFinal r →
      runConfig f₂ c = r := by
  intro f₁
  induction f₁ generalizing c r with
  | zero =>
      intro f₂ _ h hfin
      simp [runConfig] at h
      rw [← h] at hfin
      exact absurd hfin (by simp [RunResultFinal])
  | succ k ih =>
      intro f₂ hle h hfin
      obtain ⟨j, rfl⟩ : ∃ j, f₂ = j + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
      have hkj : k ≤ j := by omega
      cases hstep : step c with
      | next c' =>
          simp only [runConfig, hstep] at h ⊢
          exact ih hkj h hfin
      | done st => simpa [runConfig, hstep] using h
      | control st control =>
          cases control <;> simpa [runConfig, hstep] using h
      | runtimeError st msg => simpa [runConfig, hstep] using h

/-- `runConfig` has a unique final result regardless of fuel. -/
theorem runConfig_final_unique {c : Config} {r₁ r₂ : RunResult} {f₁ f₂ : Nat}
    (h₁ : runConfig f₁ c = r₁) (hfin₁ : RunResultFinal r₁)
    (h₂ : runConfig f₂ c = r₂) (hfin₂ : RunResultFinal r₂) :
    r₁ = r₂ := by
  have e₁ : runConfig (max f₁ f₂) c = r₁ :=
    runConfig_mono (by omega) h₁ hfin₁
  have e₂ : runConfig (max f₁ f₂) c = r₂ :=
    runConfig_mono (by omega) h₂ hfin₂
  exact e₁.symm.trans e₂

/-- Final results of the small-step program runner are unique. -/
theorem runProgramWithState_final_unique {st : RuntimeState} {program : Program}
    {r₁ r₂ : RunResult} {f₁ f₂ : Nat}
    (h₁ : SmallStep.runProgramWithState f₁ st program = r₁) (hfin₁ : RunResultFinal r₁)
    (h₂ : SmallStep.runProgramWithState f₂ st program = r₂) (hfin₂ : RunResultFinal r₂) :
    r₁ = r₂ :=
  runConfig_final_unique h₁ hfin₁ h₂ hfin₂

/-! ### Termination transfer

The heart of the backward direction: a finite small-step run from a valid entry
state guarantees the big-step evaluator terminates (does not run out of fuel for
some fuel budget). -/

theorem termination_transfer {st : RuntimeState} {program : Program}
    {o : StepResult} (hst : st.stopped = false)
    (h : ConfigRuns ⟨st, ProgramTerm.ofProgram program⟩ o) :
    ∃ fb, ResultNotFuel (evalProgramItems fb st program) := by
  sorry

/-- When the big-step evaluator does not exhaust its fuel, the program runner
returns a non-`outOfFuel` (final) result. -/
theorem runProgramWithState_final_of_notFuel {fb : Nat} {st : RuntimeState}
    {program : Program} (h : ResultNotFuel (evalProgramItems fb st program)) :
    RunResultFinal (Bc.runProgramWithState fb st program) := by
  unfold Bc.runProgramWithState
  cases hev : evalProgramItems fb st program with
  | ok st' c => simp [RunResultFinal]
  | outOfFuel st' => rw [hev] at h; simp [ResultNotFuel] at h
  | runtimeError st' msg => simp [RunResultFinal]

end BigSmall

end Bc
